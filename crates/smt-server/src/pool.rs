use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use smt_wire::BinaryRequest;

use crate::backend::{Backend, QueryResult};

/// A small backend pool that keeps structurally similar stateless requests on
/// the same backend instance. This is the protocol-invisible hook for warm
/// solver instances and future learned-clause locality.
pub struct PooledBackend {
    backends: Vec<Arc<dyn Backend>>,
}

impl PooledBackend {
    pub fn new(backends: Vec<Arc<dyn Backend>>) -> Self {
        Self { backends }
    }

    pub fn route_index(&self, request: &BinaryRequest) -> Option<usize> {
        if self.backends.is_empty() {
            return None;
        }
        let mut hasher = DefaultHasher::new();
        request.envelope.command.hash(&mut hasher);
        request.envelope.flags.hash(&mut hasher);
        request.envelope.budget_ms.hash(&mut hasher);
        request.envelope.target_node.hash(&mut hasher);
        request.expression.hash(&mut hasher);
        request.assertion_roots.hash(&mut hasher);
        request.named_assertion_refs.hash(&mut hasher);
        request.assumption_roots.hash(&mut hasher);
        Some((hasher.finish() as usize) % self.backends.len())
    }
}

impl Backend for PooledBackend {
    fn name(&self) -> &'static str {
        "pooled"
    }

    fn handle(&self, request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        let Some(index) = self.route_index(request) else {
            return Ok(QueryResult::unknown("backend pool is empty"));
        };
        self.backends[index].handle(request)
    }
}
