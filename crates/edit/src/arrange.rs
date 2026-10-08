//! Edit a PDF ▸ Arrange: change where an image sits in the page's painting order (Acrobat's
//! Bring to Front, Bring Forward, Send Backward and Send to Back).
//!
//! In PDF, stacking order *is* content order: what is painted later covers what was painted
//! earlier (ISO 32000-2 §8.1). Arranging an image therefore moves its `Do` to another place in
//! the page's content streams. The graphics state it was painted in travels with it: the snippet
//! put at the new place is
//!
//! ```text
//! [enclosing marked content…] q [gs…] [clips…] cm [fill colour] /Im Do Q [EMC…]
//! ```
//!
//! re-creating its transform, the `ExtGState`s (opacity, blend mode, soft mask) and clipping
//! paths in effect, the fill colour (which stencil masks paint with) and the marked content
//! around it (structure tags with their MCIDs, optional-content layers). Only places where the
//! state already in effect is a *prefix* of the image's own are used, so nothing in effect there
//! (another clip, another opacity, someone else's tag) can change how it looks; a text object or
//! a half-built path is never split. When no such place exists, the page's content is wrapped in
//! `q … Q` and the image is drawn after it in a stream of its own.
//!
//! "Forward" and "backward" are relative to what the image overlaps: Bring Forward moves it
//! above the next thing drawn over it (an image, form, path, shading or line of text), Bring to
//! Front above the last; Send Backward and Send to Back mirror that. Page marks (headers and
//! footers, watermarks, backgrounds) are not stacked against, and an image inside one can't be
//! arranged. An image added with Add content is a stream of its own drawn from the default state,
//! so that whole stream moves, unchanged, to a stream boundary where the default state holds.
//! Only the streams that change are rewritten, as new objects, and every byte of them outside the
//! moved operators is kept.

use std::collections::HashSet;

use pdfcraft_content::{Matrix, Op, overlaps, parse, serialize_ops};
use pdfcraft_cos::{Dict, Document, Object, Stream};

use crate::added::TAG as ADDED;
use crate::text::splice;
use crate::{EditError, stream_tag};

/// Where to move an image in the stacking order.
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

/// Painting operators (§8.5.3, §8.7.4.2, §8.8, §9.4.3, §8.9.7).
fn paints(op: &[u8]) -> bool {
    matches!(op, b"S" | b"s" | b"f" | b"F" | b"f*" | b"B" | b"B*" | b"b" | b"b*" | b"sh" | b"Do" | b"BI" | b"Tj" | b"TJ" | b"'" | b"\"")
}

fn path_paint(op: &[u8]) -> bool {
    matches!(op, b"S" | b"s" | b"f" | b"F" | b"f*" | b"B" | b"B*" | b"b" | b"b*" | b"n")
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

/// The parts of the graphics state that travel with an image.
#[derive(Clone, Default)]
struct Gs {
    ctm: Matrix,
    clips: Vec<Clip>,
    /// `gs` operators in effect (where, the CTM then — soft masks depend on it — and the op).
    ext: Vec<(usize, Matrix, Op)>,
    /// The fill colour: `cs` and `sc`/`scn`, or `g`/`rg`/`k`.
    fill: Vec<Op>,
    intent: Option<Op>,
}

/// The interpreter's state before an operator.
#[derive(Clone, Default)]
struct State {
    gs: Gs,
    stack: Vec<Gs>,
    /// Open marked-content sequences (where each began, and its `BMC`/`BDC`).
    marked: Vec<(usize, Op)>,
    in_text: bool,
    path: Vec<Op>,
    clip: Option<Op>,
}

impl State {
    /// Apply operator `op` (flat index `at`). Errors only when nesting is too deep.
    fn step(&mut self, at: usize, op: &Op) -> Result<(), EditError> {
        match op.op.as_slice() {
            b"q" => {
                if self.stack.len() >= MAX_DEPTH {
                    return Err(EditError::Invalid("the page's graphics states are nested too deeply to rearrange".into()));
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
            b"cs" => self.gs.fill = vec![op.clone()],
            b"sc" | b"scn" => {
                self.gs.fill.retain(|o| o.is("cs"));
                self.gs.fill.push(op.clone());
            }
            b"g" | b"rg" | b"k" => self.gs.fill = vec![op.clone()],
            b"ri" => self.gs.intent = Some(op.clone()),
            b"BT" => self.in_text = true,
            b"ET" => self.in_text = false,
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
            _ => {}
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

/// The box `op` paints in user space, if it paints.
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

/// Move image `index` (from [`crate::page_images`]) on `page` (0-based). Returns its new index.
pub fn arrange_image(doc: &mut Document, page: usize, index: usize, how: Arrange) -> Result<usize, EditError> {
    let images = crate::images::page_images(doc, page)?;
    let img = images.get(index).cloned().ok_or_else(|| EditError::Invalid(format!("page {} has no image {}", page + 1, index + 1)))?;
    let p = pdfcraft_model::pages(doc).into_iter().nth(page).ok_or(EditError::NoSuchPage(page))?;
    let resources = p.dict.get(b"Resources").map(|r| doc.resolve(r)).and_then(|r| r.as_dict().cloned()).unwrap_or_default();
    let xobjects = resources.get(b"XObject").map(|x| doc.resolve(x)).and_then(|x| x.as_dict().cloned()).unwrap_or_default();
    let pieces = pieces(doc, &p.dict);
    let flat: Vec<At> = pieces.iter().enumerate().flat_map(|(pi, pc)| (0..pc.ops.len()).map(move |oi| (pi, oi))).collect();
    let op_at = |&(pi, oi): &At| pieces.get(pi).and_then(|pc| pc.ops.get(oi));
    let target = flat
        .iter()
        .position(|a| *a == (img.stream, img.op))
        .ok_or_else(|| EditError::Invalid("the image could not be found in the page content".into()))?;
    let home = pieces.get(img.stream).ok_or_else(|| EditError::Invalid("the image could not be found in the page content".into()))?;
    // An item added with Add content is its own stream, drawn from the default state: the whole
    // stream moves, unchanged, to a stream boundary where that state is in effect.
    let whole = match home.tag.as_deref() {
        None => false,
        Some(ADDED) => true,
        Some(_) => return Err(EditError::Invalid("this image belongs to a header, footer, watermark or background, so it can't be arranged".into())),
    };
    let offsets: Vec<usize> = pieces.iter().scan(0usize, |n, pc| Some(std::mem::replace(n, n.saturating_add(pc.ops.len())))).collect();
    let mine_piece = |k: usize| whole && flat.get(k).is_some_and(|a| a.0 == img.stream);

    // Pass 1: the image's state, and everything painted with its box.
    let mut st = State::default();
    let mut drawn: Vec<(usize, [f64; 4])> = Vec::new();
    let mut at_image: Option<State> = None;
    for (k, a) in flat.iter().enumerate() {
        let Some(op) = op_at(a) else { continue };
        if k == target {
            at_image = Some(st.clone());
        }
        let stacked = pieces.get(a.0).is_some_and(|pc| pc.tag.as_deref().is_none_or(|t| t == ADDED)) && !mine_piece(k);
        if stacked
            && k != target
            && paints(&op.op)
            && !matches!(op.op.as_slice(), b"Tj" | b"TJ" | b"'" | b"\"")
            && let Some(b) = painted_box(doc, &xobjects, &st, op)
        {
            drawn.push((k, b));
        }
        st.step(k, op)?;
    }
    let mine = if whole { Some(State::default()) } else { at_image };
    let mine = mine.ok_or_else(|| EditError::Invalid("the image could not be found in the page content".into()))?;
    // Text, a line at a time, at its last showing operator.
    for line in crate::text::text_lines(doc, page)? {
        let stacked = pieces.get(line.stream).is_some_and(|pc| pc.tag.as_deref().is_none_or(|t| t == ADDED)) && !(whole && line.stream == img.stream);
        if let (true, Some(&last)) = (stacked, line.ops.iter().max())
            && let Some(k) = flat.iter().position(|a| *a == (line.stream, last))
        {
            drawn.push((k, line.rect));
        }
    }
    drawn.sort_by_key(|d| d.0);
    let over: Vec<usize> = drawn.iter().filter(|(_, b)| overlaps(*b, img.rect, 0.01)).map(|(k, _)| *k).collect();
    let (after, before): (Vec<usize>, Vec<usize>) = over.iter().partition(|k| **k > target);
    let pivot = match how {
        Arrange::BringToFront => after.last(),
        Arrange::BringForward => after.first(),
        Arrange::SendBackward => before.last(),
        Arrange::SendToBack => before.first(),
    };
    let Some(&pivot) = pivot else {
        return Err(EditError::Invalid(
            if how.forward() {
                "the image is already in front of everything it overlaps"
            } else {
                "the image is already behind everything it overlaps"
            }
            .into(),
        ));
    };

    // What leaves its old place: the `Do`, and marked content left empty around it.
    let mut removed: HashSet<usize> = if whole { (0..flat.len()).filter(|k| mine_piece(*k)).collect() } else { HashSet::from([target]) };
    for (bdc, op) in mine.marked.iter().rev() {
        let mut depth = 0usize;
        let mut end = None;
        let mut painting = false;
        for (k, a) in flat.iter().enumerate().skip(bdc.saturating_add(1)) {
            let Some(o) = op_at(a) else { continue };
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
                return Err(EditError::Invalid("this image is tagged together with other content, so it can't be moved on its own".into()));
            }
            _ => {}
        }
    }
    let rewritten: HashSet<usize> = if whole { HashSet::new() } else { removed.iter().filter_map(|k| flat.get(*k)).map(|a| a.0).collect() };

    // Pass 2: where the snippet can go. Positions are "before flat operator k" (k = len: the end).
    let kept: Vec<usize> = (0..flat.len()).filter(|k| !removed.contains(k)).collect();
    let clip_ids: Vec<usize> = mine.gs.clips.iter().map(|c| c.at).collect();
    let ext_ids: Vec<usize> = mine.gs.ext.iter().map(|e| e.0).collect();
    let mark_ids: Vec<usize> = mine.marked.iter().map(|m| m.0).collect();
    let mut st = State::default();
    let mut fits: Vec<Option<State>> = Vec::with_capacity(kept.len() + 1);
    for (j, &k) in kept.iter().chain(std::iter::once(&usize::MAX)).enumerate() {
        let prev = j.checked_sub(1).and_then(|i| kept.get(i)).and_then(|k| flat.get(*k));
        let next = flat.get(k);
        let place_ok = match (prev, next) {
            (Some(a), Some(b)) if a.0 == b.0 => !whole && pieces.get(a.0).is_some_and(|pc| pc.tag.is_none() && pc.skipped == 0),
            _ => {
                prev.is_none_or(|a| pieces.get(a.0).is_some_and(|pc| pc.clean_end))
                    && next.is_none_or(|b| pieces.get(b.0).is_some_and(|pc| pc.clean_start))
            }
        };
        let prefix = |have: Vec<usize>, want: &[usize]| want.starts_with(&have);
        let ok = place_ok
            && !st.in_text
            && st.path.is_empty()
            && st.clip.is_none()
            && st.gs.ctm.invert().is_some()
            && (!whole || st.gs.ctm == Matrix::IDENTITY)
            && prefix(st.gs.clips.iter().map(|c| c.at).collect(), &clip_ids)
            && prefix(st.gs.ext.iter().map(|e| e.0).collect(), &ext_ids)
            && prefix(st.marked.iter().map(|m| m.0).collect(), &mark_ids);
        fits.push(ok.then(|| st.clone()));
        if let Some(op) = next.and_then(op_at) {
            st.step(k, op)?;
        }
    }
    let end_depth = st.stack.len();
    // The kept position just after (forward) or at (backward) the pivot.
    let pj = kept.iter().position(|k| *k == pivot).unwrap_or(0);
    let chosen = if how.forward() {
        (pj + 1..fits.len()).find(|j| fits.get(*j).is_some_and(Option::is_some))
    } else {
        (0..=pj).rev().find(|j| fits.get(*j).is_some_and(Option::is_some))
    };

    // Build the snippet for the state at the chosen place (the default state for the fallback).
    let there = chosen.and_then(|j| fits.get(j).cloned().flatten()).unwrap_or_default();
    let image_op =
        flat.get(target).and_then(op_at).cloned().ok_or_else(|| EditError::Invalid("the image could not be found in the page content".into()))?;
    let mask = img.object.map(|r| doc.get(r)).is_some_and(|o| o.as_dict().is_some_and(|d| matches!(d.get(b"ImageMask"), Some(Object::Bool(true)))));
    let snippet = snippet(&mine, &there, image_op, mask)?;
    // A new stream holding `ops`, or (for an added item) its own stream.
    let mut stream_for = |ops: &[Op]| {
        if whole { home.obj.clone() } else { Object::Ref(doc.add(Object::Stream(Stream::flate(Dict::new(), &serialize_ops(ops))))) }
    };

    // Write it: rewrite changed streams, add new ones.
    let mut inserts: Vec<(At, Vec<Op>)> = Vec::new();
    let mut new_streams: Vec<(usize, Object)> = Vec::new();
    let mut wrap = false;
    match chosen {
        Some(j) => {
            let prev = j.checked_sub(1).and_then(|i| kept.get(i)).and_then(|k| flat.get(*k)).copied();
            let next = kept.get(j).and_then(|k| flat.get(*k)).copied();
            match (prev, next) {
                (Some(a), Some(b)) if a.0 == b.0 => inserts.push((b, snippet)),
                (Some(a), _) => new_streams.push((a.0 + 1, stream_for(&snippet))),
                (None, Some(b)) => new_streams.push((b.0, stream_for(&snippet))),
                (None, None) => new_streams.push((pieces.len(), stream_for(&snippet))),
            }
        }
        None if how.forward() => {
            wrap = true;
            let close: Vec<Op> = (0..end_depth.saturating_add(1)).map(|_| Op::new("Q", vec![])).collect();
            if whole {
                new_streams.push((pieces.len(), Object::Ref(doc.add(Object::Stream(Stream::flate(Dict::new(), &serialize_ops(&close)))))));
                new_streams.push((pieces.len(), home.obj.clone()));
            } else {
                new_streams.push((pieces.len(), stream_for(&[close, snippet].concat())));
            }
        }
        // Position 0 is always open, so a backward move always finds a place.
        None => return Err(EditError::Invalid("there is no place to move the image to".into())),
    }
    let touched: HashSet<usize> = rewritten.iter().copied().chain(inserts.iter().map(|((pi, _), _)| *pi)).collect();
    if touched.iter().any(|pi| pieces.get(*pi).is_some_and(|pc| pc.skipped > 0)) {
        return Err(EditError::Invalid("part of the page's content can't be read, so it isn't rewritten".into()));
    }
    let mut list: Vec<Object> = Vec::with_capacity(pieces.len() + 3);
    let mut extra = new_streams.into_iter().peekable();
    for (pi, pc) in pieces.iter().enumerate() {
        while let Some((_, obj)) = extra.next_if(|(at, _)| *at == pi) {
            list.push(obj);
        }
        if whole && pi == img.stream {
            continue;
        }
        if !touched.contains(&pi) {
            list.push(pc.obj.clone());
            continue;
        }
        let data = splice(&pc.data, &pc.ops, |oi| {
            let insert = inserts.iter().find(|(a, _)| *a == (pi, oi)).map(|(_, ops)| ops.clone()).unwrap_or_default();
            let keep = !offsets.get(pi).is_some_and(|o| removed.contains(&o.saturating_add(oi)));
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

    // Its new index: the image drawn with the same object and placement.
    let now = crate::images::page_images(doc, page)?;
    let same =
        |i: &crate::PageImage| i.object == img.object && i.name == img.name && i.matrix.iter().zip(img.matrix).all(|(a, b)| (a - b).abs() < 1e-4);
    Ok(now.iter().position(same).unwrap_or(index))
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
    let inv = cur.invert().ok_or_else(|| EditError::Invalid("the image's position can't be reproduced there".into()))?;
    let m = to.then(&inv);
    if !m.0.iter().all(|v| v.is_finite()) {
        return Err(EditError::Invalid("the image's position can't be reproduced there".into()));
    }
    *cur = to;
    Ok(Some(Op::new("cm", m.0.iter().map(|v| real(*v)).collect())))
}

/// The operators that draw the image as it was (`mine`) where `there` is in effect.
fn snippet(mine: &State, there: &State, image: Op, mask: bool) -> Result<Vec<Op>, EditError> {
    let fresh = |op: &Op| Op::new(&String::from_utf8_lossy(&op.op), op.operands.clone());
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
    out.extend(cm_to(&mut cur, mine.gs.ctm)?);
    if mine.gs.fill.is_empty() {
        if mask {
            out.push(Op::new("g", vec![Object::Int(0)]));
        }
    } else {
        out.extend(mine.gs.fill.iter().map(fresh));
    }
    out.extend(mine.gs.intent.as_ref().map(fresh));
    out.push(fresh(&image));
    out.push(Op::new("Q", vec![]));
    out.extend(open.iter().map(|_| Op::new("EMC", vec![])));
    Ok(out)
}
