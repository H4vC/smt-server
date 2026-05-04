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
        let mut first_conclusive: Option<(&'static str, QueryResult)> = None;
        for (name, result) in rx {
            match result {
                Ok(result) if result.is_conclusive() => {
                    if let Some((winner, previous)) = &first_conclusive {
                        if previous.status != result.status {
                            eprintln!(
                                "backend disagreement: {winner} returned {:?}, {name} returned {:?}",
                                previous.status, result.status
                            );
                        }
                    } else {
                        first_conclusive = Some((name, result));
                    }
                }
                Ok(result) => {
                    first_unknown.get_or_insert(result);
                }
                Err(err) => {
                    first_unknown.get_or_insert_with(|| QueryResult::unknown(err.to_string()));
                }
            }
        }
        if let Some((_name, result)) = first_conclusive {
            return Ok(result);
        }
        Ok(
            first_unknown
                .unwrap_or_else(|| QueryResult::unknown("all backends returned no result")),
        )
    }
}
