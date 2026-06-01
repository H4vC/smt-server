use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use smt_wire::raw::constants::RESPONSE_MAGIC;

use crate::cache::cache_key_for_payload;

pub const RECORD_DIR_ENV: &str = "SMT_SERVER_RECORD_DIR";

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

pub fn record_binary_pair(request: &[u8], response: &[u8]) {
    let Some(root) = record_root() else {
        return;
    };
    let _ = record_binary_pair_at(&root, request, response);
}

fn record_binary_pair_at(root: &Path, request: &[u8], response: &[u8]) -> io::Result<()> {
    let request = cache_key_for_payload(request);
    let response = canonical_response(response);
    let hash = blake3_hex(&request);
    let dir = root.join(&hash[0..2]).join(&hash[2..4]);
    fs::create_dir_all(&dir)?;

    let req_path = dir.join(format!("{hash}.req.bin"));
    let res_path = dir.join(format!("{hash}.res.bin"));
    if req_path.exists() && res_path.exists() {
        return Ok(());
    }

    let lock_path = dir.join(format!("{hash}.lock"));
    let lock = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&lock_path)
    {
        Ok(lock) => lock,
        Err(err) if err.kind() == io::ErrorKind::AlreadyExists => return Ok(()),
        Err(err) => return Err(err),
    };
    drop(lock);

    let result = (|| {
        write_atomic(&dir, &req_path, &request)?;
        write_atomic(&dir, &res_path, &response)?;
        Ok(())
    })();
    let _ = fs::remove_file(lock_path);
    result
}

fn record_root() -> Option<PathBuf> {
    match std::env::var_os(RECORD_DIR_ENV) {
        Some(value) if value.as_os_str().is_empty() => None,
        Some(value) => Some(PathBuf::from(value)),
        None => home_dir().map(|home| home.join(".smt-server").join("requests")),
    }
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

fn write_atomic(dir: &Path, final_path: &Path, bytes: &[u8]) -> io::Result<()> {
    if final_path.exists() {
        return Ok(());
    }
    let tmp_path = dir.join(format!(
        ".{}.{}.tmp",
        final_path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("recording"),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&tmp_path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    drop(file);
    fs::rename(&tmp_path, final_path).or_else(|err| {
        let _ = fs::remove_file(&tmp_path);
        if final_path.exists() {
            Ok(())
        } else {
            Err(err)
        }
    })
}

fn blake3_hex(bytes: &[u8]) -> String {
    let digest = blake3::hash(bytes);
    let bytes = digest.as_bytes();
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        push_hex_byte(&mut out, byte);
    }
    out
}

fn push_hex_byte(out: &mut String, byte: u8) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    out.push(HEX[(byte >> 4) as usize] as char);
    out.push(HEX[(byte & 0x0f) as usize] as char);
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt_wire::raw::{BinaryResponse, ExprBuilder};

    #[test]
    fn records_canonical_pair_deduped_by_request_id() -> Result<(), Box<dyn std::error::Error>> {
        let root = std::env::temp_dir().join(format!(
            "smt-server-recording-test-{}-{}",
            std::process::id(),
            TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = fs::remove_dir_all(&root);

        let mut builder = ExprBuilder::new();
        let assertion = builder.bool_true()?;
        builder.assert(assertion)?;
        let req1 = builder.build_solve_request(1, 0, false, false)?;
        let req2 = builder.build_solve_request(2, 0, false, false)?;
        let res1 = BinaryResponse::error(1, "first")?.encode()?;
        let res2 = BinaryResponse::error(2, "second")?.encode()?;

        record_binary_pair_at(&root, &req1, &res1)?;
        record_binary_pair_at(&root, &req2, &res2)?;

        let canonical = cache_key_for_payload(&req1);
        let hash = blake3_hex(&canonical);
        let req_path = root
            .join(&hash[0..2])
            .join(&hash[2..4])
            .join(format!("{hash}.req.bin"));
        let res_path = req_path.with_file_name(format!("{hash}.res.bin"));
        let stored_req = fs::read(&req_path)?;
        let stored_res = fs::read(&res_path)?;
        assert_eq!(&stored_req[4..8], &[0, 0, 0, 0]);
        assert_eq!(&stored_res[4..8], &[0, 0, 0, 0]);
        assert!(String::from_utf8_lossy(&stored_res).contains("first"));

        fs::remove_dir_all(root)?;
        Ok(())
    }
}
