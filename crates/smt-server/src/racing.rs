use std::sync::{mpsc, Arc};
use std::thread;
use std::time::{Duration, Instant};

use smt_wire::BinaryRequest;

use crate::backend::{Backend, QueryResult};

/// Backend that races several backend implementations and returns the first
/// conclusive result. `UNKNOWN` results are held until all backends are
/// inconclusive.
#[derive(Clone)]
pub struct RacingBackend {
    backends: Vec<Arc<dyn Backend>>,
    default_budget_ms: Option<u32>,
}

impl RacingBackend {
    pub fn new(backends: Vec<Arc<dyn Backend>>) -> Self {
        Self {
            backends,
            default_budget_ms: None,
        }
    }

    pub fn with_default_budget_ms(mut self, default_budget_ms: u32) -> Self {
        self.default_budget_ms = (default_budget_ms != 0).then_some(default_budget_ms);
        self
    }

    pub fn backends(&self) -> &[Arc<dyn Backend>] {
        &self.backends
    }
}

impl Backend for RacingBackend {
    fn name(&self) -> &'static str {
        "racing"
    }

    fn supports_qfbvsmtrs_text_fallback(&self) -> bool {
        self.backends
            .iter()
            .any(|backend| backend.supports_qfbvsmtrs_text_fallback())
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        if self.backends.is_empty() {
            return Ok(QueryResult::unknown("no backends configured"));
        }
        if self.backends.len() == 1 {
            return self.backends[0].handle(request);
        }
        let effective_budget_ms = if request.envelope.budget_ms == 0 {
            self.default_budget_ms.unwrap_or(0)
        } else {
            request.envelope.budget_ms
        };
        let (tx, rx) = mpsc::channel();
        for backend in &self.backends {
            let tx = tx.clone();
            let backend = Arc::clone(backend);
            let mut request = request.clone();
            if request.envelope.budget_ms == 0 {
                request.envelope.budget_ms = effective_budget_ms;
            }
            thread::spawn(move || {
                let result = backend.handle(&request);
                let _ = tx.send((backend.name(), result));
            });
        }
        drop(tx);
        let deadline = racing_deadline(effective_budget_ms);
        let mut first_unknown = None;
        while let Some((name, result)) = recv_result(&rx, deadline) {
            match result {
                Ok(result) if result.is_conclusive_for(request) => {
                    let winner_status = result.status;
                    thread::spawn(move || {
                        for (other_name, other_result) in rx {
                            if let Ok(other_result) = other_result {
                                if other_result.is_conclusive()
                                    && other_result.status != winner_status
                                {
                                    eprintln!(
                                        "backend disagreement: {name} returned {:?}, {other_name} returned {:?}",
                                        winner_status, other_result.status
                                    );
                                }
                            }
                        }
                    });
                    return Ok(result);
                }
                Ok(result) => {
                    if result.is_conclusive() {
                        first_unknown.get_or_insert_with(|| {
                            QueryResult::unknown(
                                "backend returned conclusive result without requested artifact",
                            )
                        });
                    } else {
                        first_unknown.get_or_insert(result);
                    }
                }
                Err(err) => {
                    first_unknown.get_or_insert_with(|| QueryResult::unknown(err.to_string()));
                }
            }
        }
        Ok(first_unknown.unwrap_or_else(|| {
            if deadline.is_some() {
                QueryResult::unknown("racing backend deadline elapsed")
            } else {
                QueryResult::unknown("all backends returned no result")
            }
        }))
    }
}

fn racing_deadline(budget_ms: u32) -> Option<Instant> {
    (budget_ms != 0).then(|| Instant::now() + Duration::from_millis(u64::from(budget_ms)))
}

fn recv_result<T>(rx: &mpsc::Receiver<T>, deadline: Option<Instant>) -> Option<T> {
    let Some(deadline) = deadline else {
        return rx.recv().ok();
    };
    let remaining = deadline.checked_duration_since(Instant::now())?;
    rx.recv_timeout(remaining).ok()
}
