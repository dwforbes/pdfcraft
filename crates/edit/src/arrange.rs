//! Edit a PDF ▸ Arrange: change where an image or a paragraph sits in the page's painting order
//! (Acrobat's Bring to Front, Bring Forward, Send Backward and Send to Back).
//!
//! In PDF, stacking order *is* content order: what is painted later covers what was painted
//! earlier (ISO 32000-2 §8.1). Arranging therefore moves operators to another place in the page's
//! content streams, and the state they were painted in travels with them. What moves is a list
//! of *segments*: an image's `Do`, or a stretch of a text object holding a paragraph's lines
//! (with the positioning and marked content around them). At the new place the snippet
//!
//! ```text
//! [enclosing marked content…] q [gs…] [clips…] cm [colours, text state] [BT Tm] … [ET] Q [EMC…]
//! ```
//!
//! re-creates the transform, the `ExtGState`s (opacity, blend mode, soft mask), the clipping
//! paths, the colours, the text state (font, spacing, scaling, leading, rise, render mode) and
//! the text line matrix each segment started from, and the marked content around it (structure
//! tags with their MCIDs, optional-content layers). Where a stretch of text leaves a text object
//! that goes on, the state the following text relied on is put back (`Tm`, and whatever the
//! stretch changed), so the rest of the page doesn't move.
//!
//! Only places where the state already in effect is a *prefix* of the moved content's own are
//! used, so nothing in effect there (another clip, another opacity, someone else's tag) can
//! change how it looks; a text object or a half-built path is never split. When no such place
//! exists, the page's content is wrapped in `q … Q` and the snippet is drawn after it.
//!
//! "Forward" and "backward" are relative to what the content overlaps: Bring Forward moves it
//! above the next thing drawn over it (an image, form, path, shading or line of text), Bring to
//! Front above the last; Send Backward and Send to Back mirror that. Page marks (headers and
//! footers, watermarks, backgrounds) are not stacked against, and content inside one can't be
//! arranged. An item added with Add content is a stream of its own drawn from the default state,
//! so that whole stream moves, unchanged, to a stream boundary where the default state holds.
//! Only the streams that change are rewritten, as new objects, and every byte of them outside
//! the moved operators is kept.

use std::collections::{BTreeMap, HashMap, HashSet};

use pdfcraft_content::{Matrix, Op, overlaps, parse, serialize_ops};
use pdfcraft_cos::{Dict, Document, Object, Stream};

use crate::added::TAG as ADDED;
use crate::text::{TextLine, coincident_ops, splice};
use crate::{EditError, stream_tag};

/// Where to move an image or paragraph in the stacking order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arrange {
    BringToFront,
    BringForward,
    SendBackward,
    SendToBack,
}

impl Arrange {
    fn forward(self) -> bool {
        matches!(self, Arrange::BringToFront | Arrange::BringForward)
    }
}

/// Deeper `q` nesting than this is refused rather than tracked (each level copies the state).
const MAX_DEPTH: usize = 1024;

fn invalid(s: &str) -> EditError {
    EditError::Invalid(s.into())
}

/// Text-showing operators (§9.4.3).
fn shows(op: &[u8]) -> bool {
    matches!(op, b"Tj" | b"TJ" | b"'" | b"\"")
}

/// Painting operators (§8.5.3, §8.7.4.2, §8.8, §9.4.3, §8.9.7).
fn paints(op: &[u8]) -> bool {
    shows(op) || matches!(op, b"S" | b"s" | b"f" | b"F" | b"f*" | b"B" | b"B*" | b"b" | b"b*" | b"sh" | b"Do" | b"BI")
}

fn path_paint(op: &[u8]) -> bool {
    matches!(op, b"S" | b"s" | b"f" | b"F" | b"f*" | b"B" | b"B*" | b"b" | b"b*" | b"n")
}

/// Operators that position text from the line matrix (§9.4.2).
fn positions(op: &[u8]) -> bool {
    matches!(op, b"Td" | b"TD" | b"T*" | b"Tm" | b"'" | b"\"")
}

/// The single-valued graphics and text state parameters, by operator, with their defaults.
const PARAMS: [(&str, Option<&str>); 14] = [
    ("Tf", None),
    ("Tc", Some("0")),
    ("Tw", Some("0")),
    ("Tz", Some("100")),
    ("TL", Some("0")),
    ("Ts", Some("0")),
    ("Tr", Some("0")),
    ("w", Some("1")),
    ("J", Some("0")),
    ("j", Some("0")),
    ("M", Some("10")),
    ("d", Some("[] 0")),
    ("ri", None),
    ("i", None),
];

fn param_kind(op: &[u8]) -> Option<&'static str> {
    PARAMS.iter().map(|(k, _)| *k).find(|k| k.as_bytes() == op)
}

/// One of the page's content streams.
struct Piece {
    obj: Object,
    data: Vec<u8>,
    ops: Vec<Op>,
    /// The stream's `/PCMark` (a page mark or added content), if any.
    tag: Option<String>,
    /// Only whitespace or comments before the first operator / after the last: a new stream can
    /// go next to it without separating an operator from its operands.
    clean_start: bool,
    clean_end: bool,
    /// Bytes the parser couldn't read; such a stream is never rewritten.
    skipped: usize,
}

fn blank(bytes: &[u8]) -> bool {
    let mut comment = false;
    for &b in bytes {
        match b {
            b'%' => comment = true,
            b'\n' | b'\r' => comment = false,
            _ if comment || b.is_ascii_whitespace() || b == 0 => {}
            _ => return false,
        }
    }
    true
}

fn pieces(doc: &Document, page: &Dict) -> Vec<Piece> {
    let list: Vec<Object> = match page.get(b"Contents") {
        None => Vec::new(),
        Some(c) => match &*doc.resolve(c) {
            Object::Array(a) => a.clone(),
            _ => vec![c.clone()],
        },
    };
    list.into_iter()
        .map(|obj| {
            let data = match &*doc.resolve(&obj) {
                Object::Stream(s) => s.decoded().unwrap_or_default(),
                _ => Vec::new(),
            };
            let parsed = parse(&data);
            let start = parsed.ops.first().map_or(data.len(), |o| o.span.start);
            let end = parsed.ops.last().map_or(0, |o| o.span.end);
            let clean_start = blank(data.get(..start).unwrap_or_default());
            let clean_end = blank(data.get(end..).unwrap_or_default());
            let tag = stream_tag(doc, &obj);
            Piece { obj, data, ops: parsed.ops, tag, clean_start, clean_end, skipped: parsed.skipped }
        })
        .collect()
}

/// A clipping path in effect: where it was set, the CTM then, its construction and `W`/`W*`.
#[derive(Clone)]
struct Clip {
    at: usize,
    ctm: Matrix,
    path: Vec<Op>,
    rule: Op,
}

/// The graphics state, as far as moved content needs it.
#[derive(Clone, Default)]
struct Gs {
    ctm: Matrix,
    clips: Vec<Clip>,
    /// `gs` operators in effect (where, the CTM then — soft masks depend on it — and the op).
    ext: Vec<(usize, Matrix, Op)>,
    /// The fill colour (`cs` and `sc`/`scn`, or `g`/`rg`/`k`) and the stroke colour.
    fill: Vec<Op>,
    stroke: Vec<Op>,
    /// The last operator setting each of [`PARAMS`].
    params: BTreeMap<&'static str, Op>,
}

/// The interpreter's state before an operator.
#[derive(Clone, Default)]
struct State {
    gs: Gs,
    stack: Vec<Gs>,
    /// Open marked-content sequences (where each began, and its `BMC`/`BDC`).
    marked: Vec<(usize, Op)>,
    in_text: bool,
    /// The text line matrix, and whether the text matrix still equals it (nothing shown since).
    tlm: Matrix,
    fresh: bool,
    path: Vec<Op>,
    clip: Option<Op>,
}

/// Set a colour: `space` (`cs`/`CS`) starts it afresh, a value keeps the space it is in.
fn colour(list: &mut Vec<Op>, space: &str, op: &Op) {
    if op.is(space) {
        *list = vec![op.clone()];
    } else {
        list.retain(|o| o.is(space));
        list.push(op.clone());
    }
}

impl State {
    fn leading(&self) -> f64 {
        self.gs.params.get("TL").and_then(|o| o.num(0)).unwrap_or(0.0)
    }

    fn next_line(&mut self, tx: f64, ty: f64) {
        self.tlm = Matrix::translate(tx, ty).then(&self.tlm);
        self.fresh = true;
    }

    /// Apply operator `op` (flat index `at`). Errors only when nesting is too deep.
    fn step(&mut self, at: usize, op: &Op) -> Result<(), EditError> {
        let n = pdfcraft_content::num;
        match op.op.as_slice() {
            b"q" => {
                if self.stack.len() >= MAX_DEPTH {
                    return Err(invalid("the page's graphics states are nested too deeply to rearrange"));
                }
                self.stack.push(self.gs.clone());
            }
            b"Q" => {
                if let Some(g) = self.stack.pop() {
                    self.gs = g;
                }
            }
            b"cm" => {
                if let Some(m) = op.nums::<6>() {
                    self.gs.ctm = Matrix(m).then(&self.gs.ctm);
                }
            }
            b"gs" => self.gs.ext.push((at, self.gs.ctm, op.clone())),
            b"cs" | b"sc" | b"scn" => colour(&mut self.gs.fill, "cs", op),
            b"g" | b"rg" | b"k" => self.gs.fill = vec![op.clone()],
            b"CS" | b"SC" | b"SCN" => colour(&mut self.gs.stroke, "CS", op),
            b"G" | b"RG" | b"K" => self.gs.stroke = vec![op.clone()],
            b"BT" => {
                self.in_text = true;
                self.tlm = Matrix::IDENTITY;
                self.fresh = true;
            }
            b"ET" => self.in_text = false,
            b"Tm" => {
                if let Some(m) = op.nums::<6>() {
                    self.tlm = Matrix(m);
                }
                self.fresh = true;
            }
            b"Td" => {
                if let Some([x, y]) = op.nums::<2>() {
                    self.next_line(x, y);
                }
            }
            b"TD" => {
                if let Some([x, y]) = op.nums::<2>() {
                    self.gs.params.insert("TL", Op::new("TL", vec![n(-y)]));
                    self.next_line(x, y);
                }
            }
            b"T*" => self.next_line(0.0, -self.leading()),
            b"'" => {
                self.next_line(0.0, -self.leading());
                self.fresh = false;
            }
            b"\"" => {
                if let (Some(w), Some(c)) = (op.num(0), op.num(1)) {
                    self.gs.params.insert("Tw", Op::new("Tw", vec![n(w)]));
                    self.gs.params.insert("Tc", Op::new("Tc", vec![n(c)]));
                }
                self.next_line(0.0, -self.leading());
                self.fresh = false;
            }
            b"Tj" | b"TJ" => self.fresh = false,
            b"BMC" | b"BDC" => self.marked.push((at, op.clone())),
            b"EMC" => {
                self.marked.pop();
            }
            b"m" | b"l" | b"c" | b"v" | b"y" | b"h" | b"re" => self.path.push(op.clone()),
            b"W" | b"W*" => self.clip = Some(op.clone()),
            o if path_paint(o) => {
                if let Some(rule) = self.clip.take() {
                    self.gs.clips.push(Clip { at, ctm: self.gs.ctm, path: std::mem::take(&mut self.path), rule });
                }
                self.path.clear();
            }
            o => {
                if let Some(k) = param_kind(o) {
                    self.gs.params.insert(k, op.clone());
                }
            }
        }
        Ok(())
    }

    /// The user-space box of the current path.
    fn path_box(&self) -> Option<[f64; 4]> {
        let mut pts = Vec::new();
        for op in &self.path {
            match op.op.as_slice() {
                b"re" => {
                    if let Some([x, y, w, h]) = op.nums::<4>() {
                        pts.extend([(x, y), (x + w, y + h)]);
                    }
                }
                b"m" | b"l" | b"c" | b"v" | b"y" => {
                    for pair in op.operands.chunks(2) {
                        if let [a, b] = pair
                            && let (Some(x), Some(y)) = (a.as_f64(), b.as_f64())
                        {
                            pts.push((x, y));
                        }
                    }
                }
                _ => {}
            }
        }
        let (xs, ys): (Vec<f64>, Vec<f64>) = pts.into_iter().unzip();
        let r = [
            xs.iter().copied().fold(f64::MAX, f64::min),
            ys.iter().copied().fold(f64::MAX, f64::min),
            xs.iter().copied().fold(f64::MIN, f64::max),
            ys.iter().copied().fold(f64::MIN, f64::max),
        ];
        (r[0] <= r[2] && r[1] <= r[3]).then(|| self.gs.ctm.bbox(r))
    }
}

const EVERYWHERE: [f64; 4] = [f64::MIN, f64::MIN, f64::MAX, f64::MAX];

/// The box `op` paints in user space, if it paints (text is measured separately, by line).
fn painted_box(doc: &Document, xobjects: &Dict, st: &State, op: &Op) -> Option<[f64; 4]> {
    let unit = [0.0, 0.0, 1.0, 1.0];
    match op.op.as_slice() {
        b"BI" => Some(st.gs.ctm.bbox(unit)),
        b"sh" => Some(EVERYWHERE),
        b"Do" => {
            let x = xobjects.get(op.name(0)?)?;
            let obj = doc.resolve(x);
            let Object::Stream(s) = &*obj else { return None };
            match s.dict.name(b"Subtype") {
                Some(b"Image") => Some(st.gs.ctm.bbox(unit)),
                Some(b"Form") => {
                    let nums = |k: &[u8]| -> Vec<f64> {
                        s.dict
                            .get(k)
                            .map(|v| doc.resolve(v))
                            .and_then(|v| v.as_array().map(|a| a.iter().filter_map(Object::as_f64).collect()))
                            .unwrap_or_default()
                    };
                    let (bbox, m) = (nums(b"BBox"), nums(b"Matrix"));
                    let Ok(b) = <[f64; 4]>::try_from(bbox) else { return Some(EVERYWHERE) };
                    let m = <[f64; 6]>::try_from(m).map(Matrix).unwrap_or(Matrix::IDENTITY);
                    Some(m.then(&st.gs.ctm).bbox(b))
                }
                _ => None,
            }
        }
        o if path_paint(o) && o != b"n" => st.path_box(),
        _ => None,
    }
}

/// A position in the flattened content: piece and operator.
type At = (usize, usize);

/// A run of operators that moves (flat indexes, inclusive): an image's `Do`, or part of a text
/// object.
#[derive(Clone, Copy, Debug, PartialEq)]
struct Seg {
    start: usize,
    end: usize,
    text: bool,
}

/// What is being arranged.
#[derive(Clone, Copy)]
enum Target {
    Image(usize),
    Block(usize),
}

/// The page's content, flattened.
struct Flat {
    pieces: Vec<Piece>,
    at: Vec<At>,
    offsets: Vec<usize>,
}

impl Flat {
    fn op(&self, k: usize) -> Option<&Op> {
        let (pi, oi) = *self.at.get(k)?;
        self.pieces.get(pi)?.ops.get(oi)
    }

    fn index(&self, piece: usize, op: usize) -> Option<usize> {
        let k = self.offsets.get(piece)?.checked_add(op)?;
        (self.at.get(k) == Some(&(piece, op))).then_some(k)
    }

    fn is(&self, k: usize, op: &str) -> bool {
        self.op(k).is_some_and(|o| o.is(op))
    }

    fn tag(&self, k: usize) -> Option<&str> {
        self.at.get(k).and_then(|a| self.pieces.get(a.0)).and_then(|p| p.tag.as_deref())
    }
}

/// Move image `index` (from [`crate::page_images`]) on `page` (0-based). Returns its new index.
pub fn arrange_image(doc: &mut Document, page: usize, index: usize, how: Arrange) -> Result<usize, EditError> {
    arrange(doc, page, Target::Image(index), how)
}

/// Move paragraph `block` (from [`crate::text_blocks`]) on `page` (0-based). Returns its new index.
pub fn arrange_block(doc: &mut Document, page: usize, block: usize, how: Arrange) -> Result<usize, EditError> {
    arrange(doc, page, Target::Block(block), how)
}

/// Split the paragraph's showing operators `ours` into segments: per text object, each run of
/// them not interrupted by other painting, widened to the positioning and marked content around
/// it (but never through someone else's marked content).
fn text_segments(flat: &Flat, ours: &HashSet<usize>) -> Result<Vec<Seg>, EditError> {
    let mut segs = Vec::new();
    let mut object: Option<(usize, Vec<(usize, bool)>)> = None;
    for k in 0..flat.at.len() {
        let Some(op) = flat.op(k) else { continue };
        match op.op.as_slice() {
            b"BT" => object = Some((k, Vec::new())),
            b"ET" => {
                if let Some((bt, painted)) = object.take() {
                    object_segments(flat, bt, k, &painted, &mut segs)?;
                }
            }
            o if paints(o) => {
                if let Some((_, painted)) = object.as_mut() {
                    painted.push((k, ours.contains(&k)));
                }
            }
            _ => {}
        }
    }
    if ours.iter().any(|k| !segs.iter().any(|s: &Seg| (s.start..=s.end).contains(k))) {
        return Err(invalid("part of the paragraph is outside a complete text object, so it can't be moved"));
    }
    Ok(segs)
}

/// The first marked-content operator in `range` that closes (`EMC`) or, walking backwards, opens
/// (`BDC`/`BMC`) a sequence the range doesn't contain the other end of.
fn unmatched(flat: &Flat, range: &mut dyn Iterator<Item = usize>, closing: &[u8]) -> Option<usize> {
    let mut depth = 0usize;
    for k in range {
        let o = flat.op(k)?;
        let opens = o.is("BMC") || o.is("BDC");
        let (inward, outward) = if closing == b"EMC" { (opens, o.is("EMC")) } else { (o.is("EMC"), opens) };
        if inward {
            depth += 1;
        } else if outward {
            match depth.checked_sub(1) {
                Some(d) => depth = d,
                None => return Some(k),
            }
        }
    }
    None
}

fn object_segments(flat: &Flat, bt: usize, et: usize, painted: &[(usize, bool)], segs: &mut Vec<Seg>) -> Result<(), EditError> {
    let mut i = 0;
    while i < painted.len() {
        if !painted.get(i).is_some_and(|p| p.1) {
            i += 1;
            continue;
        }
        let mut j = i;
        while painted.get(j + 1).is_some_and(|p| p.1) {
            j += 1;
        }
        let mut start = i.checked_sub(1).and_then(|h| painted.get(h)).map_or(bt, |p| p.0 + 1);
        let mut end = painted.get(j + 1).map_or(et, |p| p.0.saturating_sub(1));
        // Marked content: drop an unmatched EMC at the front or BMC/BDC at the back.
        while let Some(k) = unmatched(flat, &mut (start..=end), b"EMC") {
            start = k + 1;
        }
        while let Some(k) = unmatched(flat, &mut (start..=end).rev(), b"BDC") {
            match k.checked_sub(1).filter(|e| *e >= start) {
                Some(e) => end = e,
                None => {
                    start = end.saturating_add(1);
                    break;
                }
            }
        }
        let run = painted.get(i..=j).unwrap_or_default();
        if start > end || run.iter().any(|p| !(start..=end).contains(&p.0)) {
            return Err(invalid("this paragraph is tagged together with other text, so it can't be moved on its own"));
        }
        segs.push(Seg { start, end, text: true });
        i = j + 1;
    }
    Ok(())
}

fn arrange(doc: &mut Document, page: usize, target: Target, how: Arrange) -> Result<usize, EditError> {
    let p = pdfcraft_model::pages(doc).into_iter().nth(page).ok_or(EditError::NoSuchPage(page))?;
    let resources = p.dict.get(b"Resources").map(|r| doc.resolve(r)).and_then(|r| r.as_dict().cloned()).unwrap_or_default();
    let xobjects = resources.get(b"XObject").map(|x| doc.resolve(x)).and_then(|x| x.as_dict().cloned()).unwrap_or_default();
    let pieces = pieces(doc, &p.dict);
    let at: Vec<At> = pieces.iter().enumerate().flat_map(|(pi, pc)| (0..pc.ops.len()).map(move |oi| (pi, oi))).collect();
    let offsets: Vec<usize> = pieces.iter().scan(0usize, |n, pc| Some(std::mem::replace(n, n.saturating_add(pc.ops.len())))).collect();
    let flat = Flat { pieces, at, offsets };
    let lines: Vec<TextLine> = crate::text::text_lines(doc, page)?;
    let missing = || invalid("the item could not be found in the page content");

    // What moves: segments, or (for added content) a whole stream.
    let (segs, whole, rect, mask, image) = match target {
        Target::Image(index) => {
            let images = crate::images::page_images(doc, page)?;
            let img = images.get(index).cloned().ok_or_else(|| EditError::Invalid(format!("page {} has no image {}", page + 1, index + 1)))?;
            let k = flat.index(img.stream, img.op).ok_or_else(missing)?;
            let whole = match flat.tag(k) {
                None => None,
                Some(ADDED) => Some(img.stream),
                Some(_) => return Err(invalid("this image belongs to a header, footer, watermark or background, so it can't be arranged")),
            };
            let mask =
                img.object.map(|r| doc.get(r)).is_some_and(|o| o.as_dict().is_some_and(|d| matches!(d.get(b"ImageMask"), Some(Object::Bool(true)))));
            let segs = if whole.is_some() { Vec::new() } else { vec![Seg { start: k, end: k, text: false }] };
            (segs, whole, img.rect, mask, Some(img))
        }
        Target::Block(block) => {
            let blocks = crate::text::text_blocks(doc, page)?;
            let b = blocks.get(block).ok_or_else(|| EditError::Invalid(format!("page {} has no paragraph {}", page + 1, block + 1)))?;
            let members: Vec<&TextLine> = b.lines.iter().filter_map(|i| lines.get(*i)).collect();
            let rects: Vec<[f64; 4]> = members.iter().map(|l| l.rect).collect();
            let mut ours: HashSet<usize> = members.iter().flat_map(|l| l.ops.iter().filter_map(|o| flat.index(l.stream, *o))).collect();
            for (stream, ops) in coincident_ops(&lines, &rects) {
                ours.extend(ops.iter().filter_map(|o| flat.index(stream, *o)));
            }
            let homes: HashSet<Option<&str>> = ours.iter().map(|k| flat.tag(*k)).collect();
            let whole = match homes.iter().next() {
                _ if homes.len() > 1 => {
                    return Err(invalid("this paragraph is drawn partly in page marks or added content, so it can't be arranged"));
                }
                None => return Err(missing()),
                Some(None) => None,
                Some(Some(ADDED)) => ours.iter().next().and_then(|k| flat.at.get(*k)).map(|a| a.0),
                Some(Some(_)) => return Err(invalid("this text belongs to a header, footer, watermark or background, so it can't be arranged")),
            };
            let segs = if whole.is_some() { Vec::new() } else { text_segments(&flat, &ours)? };
            (segs, whole, b.rect, false, None)
        }
    };
    let in_unit = |k: usize| segs.iter().any(|s| (s.start..=s.end).contains(&k)) || whole.is_some_and(|w| flat.at.get(k).is_some_and(|a| a.0 == w));
    let unit: Vec<usize> = (0..flat.at.len()).filter(|k| in_unit(*k)).collect();
    let (Some(&first), Some(&last)) = (unit.first(), unit.last()) else { return Err(missing()) };

    // Pass 1: the state at each segment's start and end, and everything else painted.
    let mut st = State::default();
    let mut drawn: Vec<(usize, [f64; 4])> = Vec::new();
    let mut starts: HashMap<usize, State> = HashMap::new();
    let mut ends: HashMap<usize, State> = HashMap::new();
    for k in 0..flat.at.len() {
        let Some(op) = flat.op(k) else { continue };
        if segs.iter().any(|s| s.start == k) {
            starts.insert(k, st.clone());
        }
        let stacked = flat.tag(k).is_none_or(|t| t == ADDED);
        if stacked
            && !in_unit(k)
            && paints(&op.op)
            && !shows(&op.op)
            && let Some(b) = painted_box(doc, &xobjects, &st, op)
        {
            drawn.push((k, b));
        }
        st.step(k, op)?;
        if segs.iter().any(|s| s.end == k) {
            ends.insert(k, st.clone());
        }
    }
    for line in &lines {
        if let Some(k) = line.ops.iter().max().and_then(|o| flat.index(line.stream, *o))
            && flat.tag(k).is_none_or(|t| t == ADDED)
            && !in_unit(k)
        {
            drawn.push((k, line.rect));
        }
    }
    drawn.sort_by_key(|d| d.0);
    let over: Vec<usize> = drawn.iter().filter(|(_, b)| overlaps(*b, rect, 0.01)).map(|(k, _)| *k).collect();
    let pivot = match how {
        Arrange::BringToFront => over.iter().rfind(|k| **k > first),
        Arrange::BringForward => over.iter().find(|k| **k > first),
        Arrange::SendBackward => over.iter().rfind(|k| **k < last),
        Arrange::SendToBack => over.iter().find(|k| **k < last),
    };
    let Some(&pivot) = pivot else {
        return Err(invalid(if how.forward() {
            "it is already in front of everything it overlaps"
        } else {
            "it is already behind everything it overlaps"
        }));
    };

    let mine = match segs.first() {
        Some(s) => starts.get(&s.start).cloned().ok_or_else(missing)?,
        None => State::default(),
    };
    let ids = |v: &State| -> (Vec<usize>, Vec<usize>, Vec<usize>) {
        (v.gs.clips.iter().map(|c| c.at).collect(), v.gs.ext.iter().map(|e| e.0).collect(), v.marked.iter().map(|m| m.0).collect())
    };
    let (clip_ids, ext_ids, mark_ids) = ids(&mine);
    // The first positioning or showing operator in `range`.
    let lead =
        |range: &mut dyn Iterator<Item = usize>| range.filter_map(|k| flat.op(k)).find(|o| shows(&o.op) || positions(&o.op) || o.is("ET")).cloned();
    for s in &segs {
        let st = starts.get(&s.start).ok_or_else(missing)?;
        let (c, e, m) = ids(st);
        if c != clip_ids || m != mark_ids || !e.starts_with(&ext_ids) {
            return Err(invalid("the paragraph's lines are drawn with different clipping, transparency or tags, so they can't be moved together"));
        }
        // Text that runs on from (or into) other text on the same line can't be separated.
        let shown_first = |o: &Op| o.is("Tj") || o.is("TJ");
        if s.text && !flat.is(s.start, "BT") && !st.fresh && lead(&mut (s.start..=s.end)).is_some_and(|o| shown_first(&o)) {
            return Err(invalid("this paragraph continues text drawn before it, so it can't be moved on its own"));
        }
        let end = ends.get(&s.end).ok_or_else(missing)?;
        if s.text && !flat.is(s.end, "ET") && !end.fresh && lead(&mut (s.end.saturating_add(1)..flat.at.len())).is_some_and(|o| shown_first(&o)) {
            return Err(invalid("text after this paragraph continues it, so it can't be moved on its own"));
        }
    }

    // What leaves its old place: the unit, and marked content left empty around it.
    let mut removed: HashSet<usize> = unit.iter().copied().collect();
    for (bdc, op) in mine.marked.iter().rev() {
        let mut depth = 0usize;
        let mut end = None;
        let mut painting = false;
        for k in bdc.saturating_add(1)..flat.at.len() {
            let Some(o) = flat.op(k) else { continue };
            match o.op.as_slice() {
                b"BMC" | b"BDC" => depth = depth.saturating_add(1),
                b"EMC" if depth == 0 => {
                    end = Some(k);
                    break;
                }
                b"EMC" => depth = depth.saturating_sub(1),
                x if paints(x) && !removed.contains(&k) => painting = true,
                _ => {}
            }
        }
        match end {
            Some(e) if !painting => {
                removed.extend([*bdc, e]);
            }
            _ if has_mcid(doc, &resources, op) => {
                return Err(invalid("this is tagged together with other content, so it can't be moved on its own"));
            }
            _ => {}
        }
    }
    // What the content after each stretch of text relied on, put back where the stretch was.
    let mut restore: HashMap<usize, Vec<(usize, Op)>> = HashMap::new();
    for s in segs.iter().filter(|s| s.text) {
        let Some(next) = (s.end.saturating_add(1)..flat.at.len()).find(|k| !removed.contains(k)) else { continue };
        let end = ends.get(&s.end).ok_or_else(missing)?;
        let (bt, et) = (flat.is(s.start, "BT"), flat.is(s.end, "ET"));
        let mut ops: Vec<(usize, Op)> = Vec::new();
        if bt && !et {
            ops.push((usize::MAX, Op::new("BT", vec![])));
        }
        let mut kinds: HashSet<&'static str> = HashSet::new();
        let (mut fill, mut stroke) = (false, false);
        for k in s.start..=s.end {
            let Some(o) = flat.op(k) else { continue };
            match o.op.as_slice() {
                b"gs" => ops.push((k, o.clone())),
                b"cs" | b"sc" | b"scn" | b"g" | b"rg" | b"k" => fill = true,
                b"CS" | b"SC" | b"SCN" | b"G" | b"RG" | b"K" => stroke = true,
                b"TD" => {
                    kinds.insert("TL");
                }
                b"\"" => kinds.extend(["Tw", "Tc"]),
                x => kinds.extend(param_kind(x)),
            }
        }
        let anon = |o: &Op| (usize::MAX, o.clone());
        if fill {
            ops.extend(end.gs.fill.iter().map(anon));
        }
        if stroke {
            ops.extend(end.gs.stroke.iter().map(anon));
        }
        ops.extend(PARAMS.iter().filter(|(k, _)| kinds.contains(k)).filter_map(|(k, _)| end.gs.params.get(k)).map(anon));
        if !et {
            ops.push((usize::MAX, Op::new("Tm", end.tlm.0.iter().map(|v| real(*v)).collect())));
        } else if !bt {
            ops.push((usize::MAX, Op::new("ET", vec![])));
        }
        restore.entry(next).or_default().extend(ops);
    }
    let rewritten: HashSet<usize> =
        if whole.is_some() { HashSet::new() } else { removed.iter().chain(restore.keys()).filter_map(|k| flat.at.get(*k)).map(|a| a.0).collect() };

    // Pass 2: where the snippet can go. Positions are "before flat operator k" (k = len: the end).
    let kept: Vec<usize> = (0..flat.at.len()).filter(|k| !removed.contains(k)).collect();
    let mut st = State::default();
    let mut fits: Vec<Option<State>> = Vec::with_capacity(kept.len() + 1);
    for (j, &k) in kept.iter().chain(std::iter::once(&usize::MAX)).enumerate() {
        if let Some(ops) = restore.get(&k) {
            for (id, op) in ops {
                st.step(*id, op)?;
            }
        }
        let prev = j.checked_sub(1).and_then(|i| kept.get(i)).and_then(|k| flat.at.get(*k));
        let next = flat.at.get(k);
        let place_ok = match (prev, next) {
            (Some(a), Some(b)) if a.0 == b.0 => whole.is_none() && flat.pieces.get(a.0).is_some_and(|pc| pc.tag.is_none() && pc.skipped == 0),
            _ => {
                !restore.contains_key(&k)
                    && prev.is_none_or(|a| flat.pieces.get(a.0).is_some_and(|pc| pc.clean_end))
                    && next.is_none_or(|b| flat.pieces.get(b.0).is_some_and(|pc| pc.clean_start))
            }
        };
        let (c, e, m) = ids(&st);
        let ok = place_ok
            && !st.in_text
            && st.path.is_empty()
            && st.clip.is_none()
            && st.gs.ctm.invert().is_some()
            && (whole.is_none() || st.gs.ctm == Matrix::IDENTITY)
            && clip_ids.starts_with(&c)
            && ext_ids.starts_with(&e)
            && mark_ids.starts_with(&m);
        fits.push(ok.then(|| st.clone()));
        if let Some(op) = flat.op(k) {
            st.step(k, op)?;
        }
    }
    let end_depth = st.stack.len();
    let pj = kept.iter().position(|k| *k == pivot).unwrap_or(0);
    let chosen = if how.forward() {
        (pj + 1..fits.len()).find(|j| fits.get(*j).is_some_and(Option::is_some))
    } else {
        (0..=pj).rev().find(|j| fits.get(*j).is_some_and(Option::is_some))
    };

    // The snippet, for the state at the chosen place (the default state for the fallback).
    let there = chosen.and_then(|j| fits.get(j).cloned().flatten()).unwrap_or_default();
    let snippet = if whole.is_some() { Vec::new() } else { snippet(&flat, &segs, &starts, &mine, &there, mask)? };
    let home = whole.and_then(|w| flat.pieces.get(w)).map(|pc| pc.obj.clone());
    let mut new_stream = |ops: &[Op]| Object::Ref(doc.add(Object::Stream(Stream::flate(Dict::new(), &serialize_ops(ops)))));
    // A new stream for the snippet, or (for added content) the item's own stream.
    let mut stream_for = |ops: &[Op], own: bool| match (&home, own) {
        (Some(obj), true) => obj.clone(),
        _ => new_stream(ops),
    };

    // Write it: rewrite changed streams, add new ones.
    let mut inserts: HashMap<At, Vec<Op>> = HashMap::new();
    for (k, ops) in &restore {
        if let Some(a) = flat.at.get(*k) {
            inserts.entry(*a).or_default().extend(ops.iter().map(|(_, o)| o.clone()));
        }
    }
    let mut new_streams: Vec<(usize, Object)> = Vec::new();
    let mut wrap = false;
    match chosen {
        Some(j) => {
            let prev = j.checked_sub(1).and_then(|i| kept.get(i)).and_then(|k| flat.at.get(*k)).copied();
            let next = kept.get(j).and_then(|k| flat.at.get(*k)).copied();
            match (prev, next) {
                (Some(a), Some(b)) if a.0 == b.0 => inserts.entry(b).or_default().extend(snippet),
                (Some(a), _) => new_streams.push((a.0 + 1, stream_for(&snippet, true))),
                (None, Some(b)) => new_streams.push((b.0, stream_for(&snippet, true))),
                (None, None) => new_streams.push((flat.pieces.len(), stream_for(&snippet, true))),
            }
        }
        None if how.forward() => {
            wrap = true;
            let close: Vec<Op> = (0..end_depth.saturating_add(1)).map(|_| Op::new("Q", vec![])).collect();
            if home.is_some() {
                // The closing Qs in a stream of their own, then the item's stream.
                new_streams.push((flat.pieces.len(), stream_for(&close, false)));
                new_streams.push((flat.pieces.len(), stream_for(&[], true)));
            } else {
                new_streams.push((flat.pieces.len(), stream_for(&[close, snippet].concat(), false)));
            }
        }
        // Position 0 is always open unless the first stream starts mid-operator.
        None => return Err(invalid("there is no place to move it to")),
    }
    let touched: HashSet<usize> = rewritten.iter().copied().chain(inserts.keys().map(|(pi, _)| *pi)).collect();
    if touched.iter().any(|pi| flat.pieces.get(*pi).is_some_and(|pc| pc.skipped > 0)) {
        return Err(invalid("part of the page's content can't be read, so it isn't rewritten"));
    }
    let mut list: Vec<Object> = Vec::with_capacity(flat.pieces.len() + 3);
    let mut extra = new_streams.into_iter().peekable();
    for (pi, pc) in flat.pieces.iter().enumerate() {
        while let Some((_, obj)) = extra.next_if(|(at, _)| *at == pi) {
            list.push(obj);
        }
        if whole == Some(pi) {
            continue;
        }
        if !touched.contains(&pi) {
            list.push(pc.obj.clone());
            continue;
        }
        let data = splice(&pc.data, &pc.ops, |oi| {
            let insert = inserts.get(&(pi, oi)).cloned().unwrap_or_default();
            let keep = !flat.offsets.get(pi).is_some_and(|o| removed.contains(&o.saturating_add(oi)));
            (insert, keep)
        });
        let mut dict = match &*doc.resolve(&pc.obj) {
            Object::Stream(s) => s.dict.clone(),
            _ => Dict::new(),
        };
        for k in [&b"Length"[..], b"Filter", b"DecodeParms"] {
            dict.remove(k);
        }
        list.push(Object::Ref(doc.add(Object::Stream(Stream::flate(dict, &data)))));
    }
    list.extend(extra.map(|(_, obj)| obj));
    if wrap {
        list.insert(0, Object::Ref(doc.add(Object::Stream(Stream::from_raw(Dict::new(), b"q\n".to_vec())))));
    }
    doc.update_dict(p.obj, |d| d.set(b"Contents".to_vec(), Object::Array(list)))?;

    // Its new number.
    let near = |a: &[f64], b: &[f64]| a.iter().zip(b).all(|(x, y)| (x - y).abs() < 1e-3);
    Ok(match (target, image) {
        (Target::Image(index), Some(img)) => {
            let now = crate::images::page_images(doc, page)?;
            now.iter().position(|i| i.object == img.object && i.name == img.name && near(&i.matrix, &img.matrix)).unwrap_or(index)
        }
        (Target::Image(index), None) => index,
        (Target::Block(block), _) => {
            let now = crate::text::text_blocks(doc, page)?;
            now.iter().position(|b| near(&b.rect, &rect)).unwrap_or(block)
        }
    })
}

/// Does marked-content operator `op` carry an MCID (inline, or in a named property list)?
fn has_mcid(doc: &Document, resources: &Dict, op: &Op) -> bool {
    match op.operands.get(1) {
        Some(Object::Dict(d)) => d.get(b"MCID").is_some(),
        Some(Object::Name(n)) => resources
            .get(b"Properties")
            .map(|p| doc.resolve(p))
            .and_then(|p| p.as_dict().and_then(|p| p.get(n).map(|v| doc.resolve(v))).map(|v| v.as_dict().is_some_and(|d| d.get(b"MCID").is_some())))
            .unwrap_or(false),
        _ => false,
    }
}

/// A number operand, exact to a billionth (so composed matrices don't drift).
fn real(v: f64) -> Object {
    let r = (v * 1e9).round() / 1e9;
    if r.fract() == 0.0 && r.abs() < 1e15 { Object::Int(r as i64) } else { Object::Real(r) }
}

/// `cm` taking the CTM from `cur` to `to`, or nothing when they're equal.
fn cm_to(cur: &mut Matrix, to: Matrix) -> Result<Option<Op>, EditError> {
    if *cur == to {
        return Ok(None);
    }
    let inv = cur.invert().ok_or_else(|| invalid("the position can't be reproduced there"))?;
    let m = to.then(&inv);
    if !m.0.iter().all(|v| v.is_finite()) {
        return Err(invalid("the position can't be reproduced there"));
    }
    *cur = to;
    Ok(Some(Op::new("cm", m.0.iter().map(|v| real(*v)).collect())))
}

/// An operator from its source text (`[] 0 d`, `0 g`), for state defaults.
fn op_of(name: &str, operands: &str) -> Option<Op> {
    parse(format!("{operands} {name}").as_bytes()).ops.into_iter().next()
}

/// The operators that draw the segments as they were, where `there` is in effect.
fn snippet(flat: &Flat, segs: &[Seg], starts: &HashMap<usize, State>, mine: &State, there: &State, mask: bool) -> Result<Vec<Op>, EditError> {
    // A copy that keeps operands and inline-image data but no source position.
    let fresh = |op: &Op| Op { span: 0..0, ..op.clone() };
    let mut out: Vec<Op> = Vec::new();
    let open = mine.marked.get(there.marked.len()..).unwrap_or_default();
    out.extend(open.iter().map(|(_, op)| fresh(op)));
    out.push(Op::new("q", vec![]));
    let mut cur = there.gs.ctm;
    for (_, ctm, op) in mine.gs.ext.get(there.gs.ext.len()..).unwrap_or_default() {
        out.extend(cm_to(&mut cur, *ctm)?);
        out.push(fresh(op));
    }
    for c in mine.gs.clips.get(there.gs.clips.len()..).unwrap_or_default() {
        out.extend(cm_to(&mut cur, c.ctm)?);
        out.extend(c.path.iter().map(fresh));
        out.push(fresh(&c.rule));
        out.push(Op::new("n", vec![]));
    }
    for s in segs {
        let st = starts.get(&s.start).ok_or_else(|| invalid("the item could not be found in the page content"))?;
        for (_, ctm, op) in st.gs.ext.get(mine.gs.ext.len()..).unwrap_or_default() {
            out.extend(cm_to(&mut cur, *ctm)?);
            out.push(fresh(op));
        }
        out.extend(cm_to(&mut cur, st.gs.ctm)?);
        if s.text {
            // Everything text can depend on: colours, text state, line style (for outlines).
            match st.gs.fill.is_empty() {
                true => out.extend(op_of("g", "0")),
                false => out.extend(st.gs.fill.iter().map(fresh)),
            }
            match st.gs.stroke.is_empty() {
                true => out.extend(op_of("G", "0")),
                false => out.extend(st.gs.stroke.iter().map(fresh)),
            }
            for (k, default) in PARAMS {
                match st.gs.params.get(k) {
                    Some(op) => out.push(fresh(op)),
                    None => out.extend(default.and_then(|v| op_of(k, v))),
                }
            }
            if !flat.is(s.start, "BT") {
                out.push(Op::new("BT", vec![]));
                out.push(Op::new("Tm", st.tlm.0.iter().map(|v| real(*v)).collect()));
            }
        } else {
            match (st.gs.fill.is_empty(), mask) {
                (true, true) => out.extend(op_of("g", "0")),
                (true, false) => {}
                (false, _) => out.extend(st.gs.fill.iter().map(fresh)),
            }
            out.extend(st.gs.params.get("ri").map(fresh));
        }
        out.extend((s.start..=s.end).filter_map(|k| flat.op(k)).map(fresh));
        if s.text && !flat.is(s.end, "ET") {
            out.push(Op::new("ET", vec![]));
        }
    }
    out.push(Op::new("Q", vec![]));
    out.extend(open.iter().map(|_| Op::new("EMC", vec![])));
    Ok(out)
}
