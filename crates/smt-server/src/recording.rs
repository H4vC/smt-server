use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use rusqlite::{params, Connection};

use smt_wire::raw::constants::RESPONSE_MAGIC;

use crate::cache::cache_key_for_payload;

/// Path to the SQLite recording database. Empty disables recording.
/// Defaults to `~/.smt-server/recordings.db`.
pub const RECORD_DB_ENV: &str = "SMT_SERVER_RECORD_DB";

/// Maximum pairs committed in a single migration transaction.
const MAX_BATCH: usize = 256;

const INSERT_SQL: &str =
    "INSERT OR IGNORE INTO recordings(hash, request, response) VALUES (?1, ?2, ?3)";

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct MigrationReport {
    pub scanned: usize,
    pub inserted: usize,
    pub duplicates: usize,
    pub missing_response: usize,
    pub read_errors: usize,
    pub bad_hash: usize,
}

impl MigrationReport {
    pub fn skipped(&self) -> usize {
        self.missing_response + self.read_errors + self.bad_hash
    }
}

struct Pair {
    hash: [u8; 32],
    request: Vec<u8>,
    response: Vec<u8>,
}

impl Pair {
    fn canonical(request: &[u8], response: &[u8]) -> Self {
        let request = cache_key_for_payload(request);
        let response = canonical_response(response);
        Self::from_canonical(request, response)
    }

    fn from_canonical(request: Vec<u8>, response: Vec<u8>) -> Self {
        let hash = *blake3::hash(&request).as_bytes();
        Self {
            hash,
            request,
            response,
        }
    }
}

struct Recorder {
    conn: Mutex<Connection>,
}

impl Recorder {
    fn insert(&self, pair: &Pair) -> io::Result<()> {
        let conn = self
            .conn
            .lock()
            .map_err(|_| io::Error::other("recorder database mutex poisoned"))?;
        insert_pair(&conn, pair).map(|_| ()).map_err(sqlite_error)
    }
}

/// Persist a canonicalized request/response pair.
pub fn record_binary_pair(request: &[u8], response: &[u8]) {
    let Some(recorder) = recorder() else {
        return;
    };
    let pair = Pair::canonical(request, response);
    if let Err(err) = recorder.insert(&pair) {
        eprintln!("smt-server: failed to persist recording: {err}");
    }
}

fn recorder() -> Option<&'static Recorder> {
    static RECORDER: OnceLock<Option<Recorder>> = OnceLock::new();
    RECORDER.get_or_init(init_recorder).as_ref()
}

fn init_recorder() -> Option<Recorder> {
    let path = recording_db_path()?;
    match open_db(&path) {
        Ok(conn) => Some(Recorder {
            conn: Mutex::new(conn),
        }),
        Err(err) => {
            eprintln!("smt-server: failed to open recording db {path:?}: {err}");
            None
        }
    }
}

fn insert_pair(conn: &Connection, pair: &Pair) -> rusqlite::Result<usize> {
    conn.execute(
        INSERT_SQL,
        params![&pair.hash[..], &pair.request, &pair.response],
    )
}

/// Open (creating if needed) the recording database.
///
/// WAL mode allows readers and multiple server processes to share the same local
/// database. The busy timeout makes a process wait briefly for a serialized write
/// lock instead of failing immediately.
fn open_db(path: &Path) -> io::Result<Connection> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        std::fs::create_dir_all(parent)?;
    }
    let conn = Connection::open(path).map_err(sqlite_error)?;
    conn.pragma_update(None, "journal_mode", "WAL")
        .map_err(sqlite_error)?;
    conn.pragma_update(None, "synchronous", "NORMAL")
        .map_err(sqlite_error)?;
    conn.busy_timeout(std::time::Duration::from_secs(5))
        .map_err(sqlite_error)?;
    conn.execute_batch(
        "CREATE TABLE IF NOT EXISTS recordings (
            hash     BLOB PRIMARY KEY CHECK(length(hash) = 32),
            request  BLOB NOT NULL,
            response BLOB NOT NULL,
            created  INTEGER NOT NULL DEFAULT (unixepoch())
        ) STRICT;",
    )
    .map_err(sqlite_error)?;
    Ok(conn)
}

fn sqlite_error(err: rusqlite::Error) -> io::Error {
    io::Error::other(err)
}

pub fn recording_db_path() -> Option<PathBuf> {
    match std::env::var_os(RECORD_DB_ENV) {
        Some(value) if value.as_os_str().is_empty() => None,
        Some(value) => Some(PathBuf::from(value)),
        None => default_recording_db_path(),
    }
}

pub fn default_recording_db_path() -> Option<PathBuf> {
    home_dir().map(|home| home.join(".smt-server").join("recordings.db"))
}

pub fn default_legacy_recording_tree() -> Option<PathBuf> {
    home_dir().map(|home| home.join(".smt-server").join("requests"))
}

fn home_dir() -> Option<PathBuf> {
    std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .or_else(|| {
            let drive = std::env::var_os("HOMEDRIVE")?;
            let path = std::env::var_os("HOMEPATH")?;
            let mut out = PathBuf::from(drive);
            out.push(path);
            Some(out.into_os_string())
        })
        .map(PathBuf::from)
}

fn canonical_response(response: &[u8]) -> Vec<u8> {
    let mut out = response.to_vec();
    if out.len() >= 8 && out[..4] == RESPONSE_MAGIC {
        out[4..8].fill(0);
    }
    out
}

/// Import the default legacy file-tree corpus into the configured database.
///
/// The source is `~/.smt-server/requests`. The destination is resolved from
/// `SMT_SERVER_RECORD_DB` or defaults to `~/.smt-server/recordings.db`.
pub fn migrate_default() -> io::Result<MigrationReport> {
    let source = default_legacy_recording_tree().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            "could not determine default legacy recording directory",
        )
    })?;
    let db = recording_db_path().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            "recording database disabled; pass an explicit database path",
        )
    })?;
    migrate_tree(&source, &db)
}

/// Import `*.req.bin`/`*.res.bin` pairs under `source` into the SQLite database
/// at `db`. Existing rows are left unchanged.
pub fn migrate_tree(source: &Path, db: &Path) -> io::Result<MigrationReport> {
    let mut conn = open_db(db)?;

    let mut req_paths = Vec::new();
    collect_req_files(source, &mut req_paths)?;
    req_paths.sort();

    let mut report = MigrationReport::default();
    for chunk in req_paths.chunks(MAX_BATCH) {
        let mut batch = Vec::with_capacity(chunk.len());
        for req_path in chunk {
            report.scanned += 1;
            if let Some(pair) = read_legacy_pair(req_path, &mut report) {
                batch.push(pair);
            }
        }
        if !batch.is_empty() {
            let (inserted, duplicates) =
                insert_batch_counted(&mut conn, &batch).map_err(sqlite_error)?;
            report.inserted += inserted;
            report.duplicates += duplicates;
        }
    }
    Ok(report)
}

fn read_legacy_pair(req_path: &Path, report: &mut MigrationReport) -> Option<Pair> {
    let Some(hash) = legacy_hash_from_req_path(req_path) else {
        report.bad_hash += 1;
        return None;
    };
    let res_path = req_path.with_file_name(format!("{hash}.res.bin"));
    if !res_path.is_file() {
        report.missing_response += 1;
        return None;
    }

    let request = match std::fs::read(req_path) {
        Ok(bytes) => cache_key_for_payload(&bytes),
        Err(_) => {
            report.read_errors += 1;
            return None;
        }
    };
    let response = match std::fs::read(&res_path) {
        Ok(bytes) => canonical_response(&bytes),
        Err(_) => {
            report.read_errors += 1;
            return None;
        }
    };

    let actual_hash = blake3::hash(&request).to_hex().to_string();
    if hash != actual_hash {
        report.bad_hash += 1;
        return None;
    }

    Some(Pair::from_canonical(request, response))
}

fn legacy_hash_from_req_path(path: &Path) -> Option<&str> {
    let hash = path.file_name()?.to_str()?.strip_suffix(".req.bin")?;
    if hash.len() == 64 && hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Some(hash)
    } else {
        None
    }
}

fn insert_batch_counted(conn: &mut Connection, batch: &[Pair]) -> rusqlite::Result<(usize, usize)> {
    let tx = conn.transaction()?;
    let mut inserted = 0usize;
    let mut duplicates = 0usize;
    {
        let mut stmt = tx.prepare_cached(INSERT_SQL)?;
        for pair in batch {
            match stmt.execute(params![&pair.hash[..], &pair.request, &pair.response])? {
                0 => duplicates += 1,
                n => inserted += n,
            }
        }
    }
    tx.commit()?;
    Ok((inserted, duplicates))
}

fn collect_req_files(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(err) => return Err(err),
    };
    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            collect_req_files(&path, out)?;
        } else if path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(".req.bin"))
        {
            out.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusqlite::OptionalExtension;
    use smt_wire::raw::{BinaryResponse, ExprBuilder};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_root(prefix: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
    }

    fn read_pair(conn: &Connection, hash: &[u8]) -> Option<(Vec<u8>, Vec<u8>)> {
        conn.query_row(
            "SELECT request, response FROM recordings WHERE hash = ?1",
            params![hash],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )
        .optional()
        .unwrap()
    }

    #[test]
    fn inserts_canonical_pair_deduped_by_request_id() -> Result<(), Box<dyn std::error::Error>> {
        let root = temp_root("smt-server-recording-test");
        let db = root.join("recordings.db");
        let conn = open_db(&db)?;

        let mut builder = ExprBuilder::new();
        let assertion = builder.bool_true()?;
        builder.assert(assertion)?;
        let req1 = builder.build_solve_request(1, 0, false, false)?;
        let req2 = builder.build_solve_request(2, 0, false, false)?;
        let res1 = BinaryResponse::error(1, "first")?.encode()?;
        let res2 = BinaryResponse::error(2, "second")?.encode()?;

        let pair1 = Pair::canonical(&req1, &res1);
        let hash = pair1.hash;
        assert_eq!(insert_pair(&conn, &pair1)?, 1);
        assert_eq!(insert_pair(&conn, &Pair::canonical(&req2, &res2))?, 0);

        let (stored_req, stored_res) = read_pair(&conn, &hash).expect("row present");
        assert_eq!(&stored_req[4..8], &[0, 0, 0, 0]);
        assert_eq!(&stored_res[4..8], &[0, 0, 0, 0]);
        assert!(String::from_utf8_lossy(&stored_res).contains("first"));

        let count: i64 = conn.query_row("SELECT COUNT(*) FROM recordings", [], |row| row.get(0))?;
        assert_eq!(count, 1);

        drop(conn);
        let _ = std::fs::remove_dir_all(&root);
        Ok(())
    }

    #[test]
    fn migrates_legacy_tree_into_db() -> Result<(), Box<dyn std::error::Error>> {
        let root = temp_root("smt-server-migrate-test");
        let source = root.join("requests");
        let db = root.join("recordings.db");

        let mut builder = ExprBuilder::new();
        let assertion = builder.bool_true()?;
        builder.assert(assertion)?;
        let request = cache_key_for_payload(&builder.build_solve_request(7, 0, false, false)?);
        let response = canonical_response(&BinaryResponse::error(7, "legacy")?.encode()?);

        let hash = blake3::hash(&request).to_hex().to_string();
        let dir = source.join(&hash[0..2]).join(&hash[2..4]);
        std::fs::create_dir_all(&dir)?;
        std::fs::write(dir.join(format!("{hash}.req.bin")), &request)?;
        std::fs::write(dir.join(format!("{hash}.res.bin")), &response)?;

        let report = migrate_tree(&source, &db)?;
        assert_eq!(report.scanned, 1);
        assert_eq!(report.inserted, 1);
        assert_eq!(report.duplicates, 0);
        assert_eq!(report.skipped(), 0);

        let report = migrate_tree(&source, &db)?;
        assert_eq!(report.scanned, 1);
        assert_eq!(report.inserted, 0);
        assert_eq!(report.duplicates, 1);
        assert_eq!(report.skipped(), 0);

        let conn = open_db(&db)?;
        let key = *blake3::hash(&request).as_bytes();
        let (stored_req, stored_res) = read_pair(&conn, &key).expect("migrated row present");
        assert_eq!(stored_req, request);
        assert!(String::from_utf8_lossy(&stored_res).contains("legacy"));

        drop(conn);
        let _ = std::fs::remove_dir_all(&root);
        Ok(())
    }

    #[test]
    fn migration_reports_skipped_legacy_files() -> Result<(), Box<dyn std::error::Error>> {
        let root = temp_root("smt-server-migrate-skip-test");
        let source = root.join("requests");
        let db = root.join("recordings.db");
        std::fs::create_dir_all(&source)?;

        let missing_hash = "0".repeat(64);
        std::fs::write(
            source.join(format!("{missing_hash}.req.bin")),
            b"missing response",
        )?;

        let bad_hash = "1".repeat(64);
        std::fs::write(
            source.join(format!("{bad_hash}.req.bin")),
            b"bad hash request",
        )?;
        std::fs::write(source.join(format!("{bad_hash}.res.bin")), b"response")?;

        let report = migrate_tree(&source, &db)?;
        assert_eq!(report.scanned, 2);
        assert_eq!(report.inserted, 0);
        assert_eq!(report.duplicates, 0);
        assert_eq!(report.missing_response, 1);
        assert_eq!(report.bad_hash, 1);
        assert_eq!(report.read_errors, 0);

        let _ = std::fs::remove_dir_all(&root);
        Ok(())
    }
}
