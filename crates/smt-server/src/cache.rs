use std::collections::HashMap;
use std::sync::Mutex;

use smt_wire::{constants::RESPONSE_MAGIC, request::is_binary_request_payload};

pub const DEFAULT_MAX_CACHE_ENTRIES: usize = 4096;
pub const DEFAULT_MAX_CACHE_KEY_BYTES: usize = 1024 * 1024;
pub const DEFAULT_MAX_CACHED_RESPONSE_BYTES: usize = 16 * 1024 * 1024;

/// Simple cache counters for tests and observability.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub inserts: u64,
}

/// In-memory request/response cache for the stateless protocol.
#[derive(Debug)]
pub struct ResponseCache {
    entries: Mutex<HashMap<Vec<u8>, Vec<u8>>>,
    stats: Mutex<CacheStats>,
    max_entries: usize,
    max_key_bytes: usize,
    max_response_bytes: usize,
}

impl Default for ResponseCache {
    fn default() -> Self {
        Self::with_limits(
            DEFAULT_MAX_CACHE_ENTRIES,
            DEFAULT_MAX_CACHE_KEY_BYTES,
            DEFAULT_MAX_CACHED_RESPONSE_BYTES,
        )
    }
}

impl ResponseCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_limits(
        max_entries: usize,
        max_key_bytes: usize,
        max_response_bytes: usize,
    ) -> Self {
        Self {
            entries: Mutex::new(HashMap::new()),
            stats: Mutex::new(CacheStats::default()),
            max_entries,
            max_key_bytes,
            max_response_bytes,
        }
    }

    pub fn accepts_payload(&self, payload: &[u8]) -> bool {
        self.max_entries != 0 && payload.len() <= self.max_key_bytes
    }

    pub fn lookup(&self, key: &[u8]) -> Option<Vec<u8>> {
        let found = self.entries.lock().ok()?.get(key).cloned();
        if let Ok(mut stats) = self.stats.lock() {
            if found.is_some() {
                stats.hits += 1;
            } else {
                stats.misses += 1;
            }
        }
        found
    }

    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries.lock().ok()?.get(key).cloned()
    }

    pub fn insert(&self, key: Vec<u8>, response: Vec<u8>) {
        if self.max_entries == 0
            || key.len() > self.max_key_bytes
            || response.len() > self.max_response_bytes
        {
            return;
        }
        if let Ok(mut entries) = self.entries.lock() {
            if entries.len() >= self.max_entries {
                entries.clear();
            }
            entries.insert(key, response);
        }
        if let Ok(mut stats) = self.stats.lock() {
            stats.inserts += 1;
        }
    }

    pub fn stats(&self) -> CacheStats {
        self.stats.lock().map(|stats| *stats).unwrap_or_default()
    }

    pub fn len(&self) -> usize {
        self.entries
            .lock()
            .map(|entries| entries.len())
            .unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Build a cache key containing all fields that affect the semantic response
/// payload while excluding the binary request_id echo field.
pub fn cache_key_for_payload(payload: &[u8]) -> Vec<u8> {
    let mut key = payload.to_vec();
    if is_binary_request_payload(payload) && key.len() >= 8 {
        key[4..8].fill(0);
    }
    key
}

pub fn binary_request_id(payload: &[u8]) -> Option<u32> {
    if is_binary_request_payload(payload) && payload.len() >= 8 {
        Some(u32::from_le_bytes(payload[4..8].try_into().ok()?))
    } else {
        None
    }
}

/// Cached binary responses are stored with the response request_id produced by
/// the first equivalent request. Patch the echoed request_id for later hits.
pub fn rebind_cached_response(mut response: Vec<u8>, request_id: Option<u32>) -> Vec<u8> {
    if let Some(request_id) = request_id {
        if response.len() >= 8 && response[..4] == RESPONSE_MAGIC {
            response[4..8].copy_from_slice(&request_id.to_le_bytes());
        }
    }
    response
}
