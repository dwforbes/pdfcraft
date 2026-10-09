//! Autosave and crash recovery.
//!
//! While documents have unsaved changes, their working file is written every
//! `AUTOSAVE_SECS` to a recovery folder in the user's data directory. Each entry is
//! `<key>.pdf` plus `<key>.json` (name, original path, time). Saving, discarding or closing a
//! document removes its entry, and a clean quit leaves the folder empty. If entries are found at
//! startup, the previous session ended unexpectedly and the app offers to recover them.
//!
//! **Several running copies share the folder.** Each session's entries are keyed
//! `<session>-<doc>`, and while a session has entries it holds an OS lock on `<session>.lock`.
//! The OS releases the lock when the process ends, however it ends, so an entry whose session's
//! lock can be taken was left by a session that crashed (or by a version before session locks),
//! and one whose lock is held belongs to a copy of PdfCraft that is still running: it is never
//! offered, recovered, discarded or cleaned up by another copy.
//!
//! Encrypted documents are stored encrypted (the working file is), so recovery never writes
//! plaintext of a protected document to disk. The web build has no recovery store yet.

use std::fs::{File, TryLockError};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::PdfCraftApp;

/// How often unsaved changes are written to the recovery folder.
pub const AUTOSAVE_SECS: f64 = 60.0;

/// What a recovery entry records next to the PDF bytes.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RecoveryMeta {
    pub key: String,
    pub name: String,
    /// Where the document was saved before (Save writes back there after recovery).
    pub path: Option<String>,
    /// Seconds since the Unix epoch when the snapshot was taken.
    pub saved_at: u64,
    /// The bytes are encrypted; recovering asks for the password.
    pub encrypted: bool,
}

/// The recovery folder.
#[derive(Clone, Debug)]
pub struct RecoveryStore {
    dir: PathBuf,
}

impl RecoveryStore {
    pub fn new(dir: impl Into<PathBuf>) -> Self {
        Self { dir: dir.into() }
    }

    /// The platform's per-user data folder: `~/Library/Application Support/PdfCraft/Recovery`
    /// (macOS), `%LOCALAPPDATA%\PdfCraft\Recovery` (Windows), or
    /// `$XDG_DATA_HOME/pdfcraft/recovery` / `~/.local/share/pdfcraft/recovery` (others).
    pub fn default_dir() -> Option<PathBuf> {
        let env = |k: &str| std::env::var_os(k).filter(|v| !v.is_empty()).map(PathBuf::from);
        if cfg!(target_os = "macos") {
            env("HOME").map(|h| h.join("Library/Application Support/PdfCraft/Recovery"))
        } else if cfg!(windows) {
            env("LOCALAPPDATA").map(|d| d.join("PdfCraft").join("Recovery"))
        } else {
            env("XDG_DATA_HOME").or_else(|| env("HOME").map(|h| h.join(".local/share"))).map(|d| d.join("pdfcraft/recovery"))
        }
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Write (or replace) an entry. The PDF is written before its metadata, both atomically, so
    /// a listed entry always has complete bytes.
    pub fn write(&self, meta: &RecoveryMeta, bytes: &[u8]) -> std::io::Result<()> {
        std::fs::create_dir_all(&self.dir)?;
        crate::editing::write_atomically(&self.dir.join(format!("{}.pdf", meta.key)).to_string_lossy(), bytes)?;
        let json = serde_json::to_vec_pretty(meta).map_err(std::io::Error::other)?;
        crate::editing::write_atomically(&self.dir.join(format!("{}.json", meta.key)).to_string_lossy(), &json)
    }

    fn lock_path(&self, session: &str) -> PathBuf {
        self.dir.join(format!("{session}.lock"))
    }

    /// Does a running session own entry `key`? (Its session's lock is held.)
    pub fn is_live(&self, key: &str) -> bool {
        let Some((session, _)) = key.rsplit_once('-') else { return false };
        let Ok(file) = File::options().read(true).write(true).open(self.lock_path(session)) else { return false };
        // Taking the lock means nobody holds it; it is released again when `file` drops.
        matches!(file.try_lock(), Err(TryLockError::WouldBlock))
    }

    /// Hold `session`'s lock while it has entries. The lock file is locked under a temporary
    /// name and then renamed, so no other copy ever sees it unlocked and takes it for stale.
    pub(crate) fn claim(&self, session: &str) -> std::io::Result<SessionLock> {
        std::fs::create_dir_all(&self.dir)?;
        let path = self.lock_path(session);
        let tmp = self.dir.join(format!("{session}.lock-new"));
        let file = File::options().read(true).write(true).create(true).truncate(true).open(&tmp)?;
        match file.try_lock() {
            Ok(()) => {}
            Err(TryLockError::WouldBlock) => return Err(std::io::Error::other("the session lock is taken")),
            Err(TryLockError::Error(e)) => return Err(e),
        }
        std::fs::rename(&tmp, &path)?;
        Ok(SessionLock { _file: file, path })
    }

    /// Remove lock files (and unfinished ones) left by sessions that ended.
    fn sweep_locks(&self) {
        let Ok(dir) = std::fs::read_dir(&self.dir) else { return };
        for entry in dir.flatten() {
            let path = entry.path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default().to_owned();
            if let Some(session) = name.strip_suffix(".lock")
                && !self.is_live(&format!("{session}-0"))
            {
                let _ = std::fs::remove_file(&path);
            } else if name.ends_with(".lock-new")
                && let Ok(file) = File::options().read(true).write(true).open(&path)
                && file.try_lock().is_ok()
            {
                let _ = std::fs::remove_file(&path);
            }
        }
    }

    pub fn remove(&self, key: &str) {
        let _ = std::fs::remove_file(self.dir.join(format!("{key}.json")));
        let _ = std::fs::remove_file(self.dir.join(format!("{key}.pdf")));
    }

    /// Entries a new session may offer: those of sessions that are no longer running. Lock files
    /// of ended sessions are cleaned up.
    pub fn recoverable(&self) -> Vec<RecoveryMeta> {
        let out = self.list().into_iter().filter(|m| !self.is_live(&m.key)).collect();
        self.sweep_locks();
        out
    }

    /// Complete entries, newest first, including running sessions'. Incomplete leftovers (bytes
    /// without metadata) are removed, unless a running session may still be writing them.
    pub fn list(&self) -> Vec<RecoveryMeta> {
        let Ok(dir) = std::fs::read_dir(&self.dir) else { return Vec::new() };
        let mut out = Vec::new();
        for entry in dir.flatten() {
            let path = entry.path();
            match path.extension().and_then(|e| e.to_str()) {
                Some("json") => {
                    let meta = std::fs::read(&path).ok().and_then(|b| serde_json::from_slice::<RecoveryMeta>(&b).ok());
                    match meta {
                        Some(m) if self.dir.join(format!("{}.pdf", m.key)).is_file() => out.push(m),
                        _ if path.file_stem().and_then(|k| k.to_str()).is_some_and(|k| self.is_live(k)) => {}
                        _ => {
                            let _ = std::fs::remove_file(&path);
                        }
                    }
                }
                Some("pdf")
                    if !path.with_extension("json").is_file() && !path.file_stem().and_then(|k| k.to_str()).is_some_and(|k| self.is_live(k)) =>
                {
                    let _ = std::fs::remove_file(&path);
                }
                _ => {}
            }
        }
        out.sort_by_key(|m| std::cmp::Reverse(m.saved_at));
        out
    }

    pub fn read(&self, key: &str) -> std::io::Result<Vec<u8>> {
        std::fs::read(self.dir.join(format!("{key}.pdf")))
    }

    /// Remove every entry of sessions that are no longer running ("Discard all").
    pub fn clear(&self) {
        for m in self.recoverable() {
            self.remove(&m.key);
        }
    }
}

/// A session's hold on its entries: the locked `<session>.lock`. Dropping it (a clean quit, or the
/// session's last entry going) removes the file; if the process dies instead, the OS releases
/// the lock and the file is left for the next session to sweep.
#[derive(Debug)]
pub(crate) struct SessionLock {
    _file: File,
    path: PathBuf,
}

impl Drop for SessionLock {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

/// A session id unique on this machine: start time, process id and a per-process counter (tests
/// run several apps in one process).
pub(crate) fn new_session_id() -> String {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    format!("{}-{}-{}", now_secs(), std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed))
}

fn now_secs() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

impl PdfCraftApp {
    /// Turn on autosave into `store`, and look for documents a previous session left behind.
    pub fn enable_recovery(&mut self, store: RecoveryStore) {
        self.recoverable = store.recoverable();
        if !self.recoverable.is_empty() {
            self.dialog = Some(crate::Dialog::Recovery);
        }
        self.recovery = Some(store);
    }

    /// Write snapshots of documents changed since the last autosave (called periodically).
    pub fn autosave_now(&mut self) {
        let Some(store) = self.recovery.clone() else { return };
        let snaps = self.session.autosave_snapshots();
        if !snaps.is_empty() {
            self.hold_recovery_lock(&store);
        }
        for snap in snaps {
            let session = &self.recovery_session;
            let key = self.recovery_keys.entry(snap.doc).or_insert_with(|| format!("{session}-{}", snap.doc.0)).clone();
            let meta = RecoveryMeta { key, name: snap.name, path: snap.path, saved_at: now_secs(), encrypted: snap.encrypted };
            if let Err(e) = store.write(&meta, &snap.bytes) {
                log::warn!("autosave failed: {e}");
            }
        }
    }

    /// Take this session's lock (before writing its first entry), so other running copies leave
    /// its entries alone. Without it, entries are still written: losing work is worse.
    fn hold_recovery_lock(&mut self, store: &RecoveryStore) {
        if self.recovery_lock.is_none() {
            match store.claim(&self.recovery_session) {
                Ok(lock) => self.recovery_lock = Some(lock),
                Err(e) => log::warn!("couldn't lock the recovery session: {e}"),
            }
        }
    }

    /// Drop a document's recovery entry (it was saved, discarded or closed).
    pub(crate) fn forget_recovery(&mut self, doc: pdfcraft_engine::DocId) {
        if let (Some(store), Some(key)) = (&self.recovery, self.recovery_keys.remove(&doc)) {
            store.remove(&key);
        }
        if self.recovery_keys.is_empty() {
            self.recovery_lock = None;
        }
    }

    /// Autosave when the interval has passed (called every frame).
    pub(crate) fn autosave_tick(&mut self, now: f64) {
        if self.recovery.is_none() {
            return;
        }
        if now - self.last_autosave >= AUTOSAVE_SECS {
            self.last_autosave = now;
            self.autosave_now();
        }
    }

    /// Reopen recovered documents (`keys`), as unsaved changes at their original paths.
    pub fn recover(&mut self, keys: &[String]) {
        let Some(store) = self.recovery.clone() else { return };
        for key in keys {
            let Some(meta) = self.recoverable.iter().find(|m| &m.key == key).cloned() else { continue };
            let bytes = match store.read(key) {
                Ok(b) => b,
                Err(e) => {
                    self.notify_fmt("Couldn't recover {name}: {e}", &[("name", &meta.name), ("e", &e.to_string())]);
                    continue;
                }
            };
            if meta.encrypted {
                // The password prompt opens it; mark it recovered once it is open.
                self.pending_recovered = Some(meta.clone());
            }
            match self.open_bytes(&meta.name, None, bytes) {
                Ok(()) if self.password_prompt.is_none() => self.finish_recovery(&meta),
                Ok(()) => {}
                Err(e) => self.notify_fmt("Couldn't recover {name}: {e}", &[("name", &meta.name), ("e", &e.to_string())]),
            }
        }
        self.recoverable.retain(|m| !keys.contains(&m.key));
    }

    /// The most recently opened tab came from `meta`: keep its recovery entry and path. The entry
    /// moves under this session's key (and lock), so other copies see it as in use from now on.
    pub(crate) fn finish_recovery(&mut self, meta: &RecoveryMeta) {
        let Some((_, id)) = self.active_ids() else { return };
        self.session.mark_recovered(id, meta.path.clone());
        self.pending_recovered = None;
        let mut key = meta.key.clone();
        if let Some(store) = self.recovery.clone() {
            self.hold_recovery_lock(&store);
            let mine = format!("{}-{}", self.recovery_session, id.0);
            let moved = store.read(&meta.key).and_then(|bytes| store.write(&RecoveryMeta { key: mine.clone(), ..meta.clone() }, &bytes));
            match moved {
                Ok(()) => {
                    store.remove(&meta.key);
                    key = mine;
                }
                Err(e) => log::warn!("couldn't move the recovered entry: {e}"),
            }
        }
        self.recovery_keys.insert(id, key);
    }

    /// Delete recovery entries the user chose not to recover.
    pub fn discard_recovered(&mut self, keys: &[String]) {
        if let Some(store) = &self.recovery {
            for k in keys {
                store.remove(k);
            }
        }
        self.recoverable.retain(|m| !keys.contains(&m.key));
    }

    /// Clean shutdown: documents were saved or discarded, so nothing needs recovering.
    pub fn shutdown_recovery(&mut self) {
        if self.first_dirty().is_none()
            && let Some(store) = &self.recovery
        {
            for key in self.recovery_keys.values() {
                store.remove(key);
            }
            self.recovery_keys.clear();
            self.recovery_lock = None;
        }
    }
}
