use std::sync::{mpsc, Arc};
use std::thread;

use smt_wire::BinaryRequest;

use crate::backend::{Backend, QueryResult};

/// Backend that races several backend implementations and returns the first
/// conclusive result. `UNKNOWN` results are held until all backends are
/// inconclusive.
#[derive(Clone)]
pub struct RacingBackend {
    backends: Vec<Arc<dyn Backend>>,
}

impl RacingBackend {
    pub fn new(backends: Vec<Arc<dyn Backend>>) -> Self {
        Self { backends }
    }

    pub fn backends(&self) -> &[Arc<dyn Backend>] {
        &self.backends
    }
}

impl Backend for RacingBackend {
    fn name(&self) -> &'static str {
        "racing"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        if self.backends.is_empty() {
            return Ok(QueryResult::unknown("no backends configured"));
        }
        if self.backends.len() == 1 {
            return self.backends[0].handle(request);
        }
        let (tx, rx) = mpsc::channel();
        for backend in &self.backends {
            let tx = tx.clone();
            let backend = Arc::clone(backend);
            let request = request.clone();
            thread::spawn(move || {
                let result = backend.handle(&request);
                let _ = tx.send((backend.name(), result));
            });
        }
        drop(tx);
        let mut first_unknown = None;
        for (_name, result) in rx {
            match result {
                Ok(result) if result.is_conclusive() => return Ok(result),
                Ok(result) => {
                    first_unknown.get_or_insert(result);
                }
                Err(err) => {
                    first_unknown.get_or_insert_with(|| QueryResult::unknown(err.to_string()));
                }
            }
        }
        Ok(
            first_unknown
                .unwrap_or_else(|| QueryResult::unknown("all backends returned no result")),
        )
    }
}
