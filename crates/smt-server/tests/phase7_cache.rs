use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use smt_server::{dispatch_payload_with_cache, Backend, QueryResult, ResponseCache};
use smt_wire::{BinaryRequest, BinaryResponse, ExprBuilder};

struct CountingBackend {
    count: Arc<AtomicUsize>,
}

impl Backend for CountingBackend {
    fn name(&self) -> &'static str {
        "counting"
    }

    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        self.count.fetch_add(1, Ordering::SeqCst);
        Ok(QueryResult::sat(None))
    }
}

#[test]
fn cache_reuses_semantic_binary_query_across_request_ids_and_rebinds_echo() {
    let count = Arc::new(AtomicUsize::new(0));
    let backend = CountingBackend {
        count: Arc::clone(&count),
    };
    let cache = ResponseCache::new();

    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let req1 = builder.build_solve_request(100, 0, false, false).unwrap();
    let req2 = builder.build_solve_request(200, 0, false, false).unwrap();

    let resp1 = dispatch_payload_with_cache(&req1, &backend, Some(&cache));
    let resp2 = dispatch_payload_with_cache(&req2, &backend, Some(&cache));

    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.stats().misses, 1);
    assert_eq!(cache.stats().hits, 1);

    let resp1 = BinaryResponse::parse(&resp1).unwrap();
    let resp2 = BinaryResponse::parse(&resp2).unwrap();
    assert_eq!(resp1.envelope.request_id, 100);
    assert_eq!(resp2.envelope.request_id, 200);
}

#[test]
fn cache_key_keeps_fields_that_affect_payload() {
    let cache = ResponseCache::new();
    let count = Arc::new(AtomicUsize::new(0));
    let backend = CountingBackend {
        count: Arc::clone(&count),
    };

    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let no_model = builder.build_solve_request(1, 0, false, false).unwrap();
    let want_model = builder.build_solve_request(2, 0, true, false).unwrap();

    let _ = dispatch_payload_with_cache(&no_model, &backend, Some(&cache));
    let _ = dispatch_payload_with_cache(&want_model, &backend, Some(&cache));

    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert_eq!(cache.len(), 2);
}
