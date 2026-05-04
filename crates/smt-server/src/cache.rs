use std::collections::HashMap;
use std::sync::Mutex;

/// In-memory request/response cache for the stateless protocol.
#[derive(Debug, Default)]
pub struct ResponseCache {
    entries: Mutex<HashMap<Vec<u8>, Vec<u8>>>,
}

impl ResponseCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        self.entries.lock().ok()?.get(key).cloned()
    }

    pub fn insert(&self, key: Vec<u8>, response: Vec<u8>) {
        if let Ok(mut entries) = self.entries.lock() {
            entries.insert(key, response);
        }
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
