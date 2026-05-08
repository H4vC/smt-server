use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::{Duration, Instant};

use smt_server::{
    handle_text_frame, parse_smtlib_script, request_to_smt2, Backend, BinbitBackend,
    CancellationToken, QfbvsmtrsBackend, QueryResult, RacingBackend, SolveContext, Z3Backend,
};
use smt_wire::raw::{BinaryRequest, ExprBuilder};

#[test]
fn smtlib_text_frontend_solves_sat_and_formats_model() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (assert (= x #b01))
        (check-sat)
        (get-model)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("define-fun x"), "{text}");
    assert!(text.contains("#b01"), "{text}");
}

#[test]
fn smtlib_text_frontend_rejects_incremental_commands() {
    let script = "(set-logic QF_BV) (push 1) (check-sat)";
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("error"), "{text}");
    assert!(text.contains("push"), "{text}");
}

#[test]
fn smtlib_text_frontend_qfbvsmtrs_fallback_supports_push_pop() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (push 1)
        (assert (= x #b01))
        (pop 1)
        (assert (= x #b10))
        (check-sat)
        (get-value (x))
    "#;
    let output = handle_text_frame(script.as_bytes(), &QfbvsmtrsBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("((x #b10))"), "{text}");
}

#[test]
fn smtlib_text_frontend_racing_backend_uses_qfbvsmtrs_fallback() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (push 1)
        (assert (= x #b01))
        (pop 1)
        (assert (= x #b10))
        (check-sat)
        (get-value (x))
    "#;
    let racing = RacingBackend::new(vec![Arc::new(BinbitBackend), Arc::new(QfbvsmtrsBackend)]);
    let output = handle_text_frame(script.as_bytes(), &racing).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("((x #b10))"), "{text}");
}

#[test]
fn smtlib_text_frontend_qfbvsmtrs_fallback_reports_original_and_fallback_errors() {
    let script = "(set-logic QF_BV) (push bad) (check-sat)";
    let output = handle_text_frame(script.as_bytes(), &QfbvsmtrsBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("error"), "{text}");
    assert!(text.contains("qfbvsmtrs fallback"), "{text}");
}

#[test]
fn smtlib_text_frontend_get_value_formats_value_response() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (assert (= x #b10))
        (check-sat)
        (get-value (x))
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("((x #b10))"), "{text}");
}

#[test]
fn smtlib_text_frontend_rejects_get_value_unknown_symbol() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 1))
        (assert (= x #b1))
        (check-sat)
        (get-value (y))
    "#;
    for backend in [
        &BinbitBackend as &dyn Backend,
        &QfbvsmtrsBackend as &dyn Backend,
    ] {
        let output = handle_text_frame(script.as_bytes(), backend).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("error"), "{text}");
        assert!(text.contains("y"), "{text}");
    }
}

#[test]
fn smtlib_text_frontend_get_value_keeps_unconstrained_symbol_live() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (check-sat)
        (get-value (x))
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("((x #b"), "{text}");
}

#[test]
fn smtlib_text_frontend_named_unsat_core() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const p Bool)
        (assert (! p :named p_true))
        (assert (! (not p) :named p_false))
        (check-sat)
        (get-unsat-core)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unsat\n"), "{text}");
    assert!(text.contains("p_true"), "{text}");
    assert!(text.contains("p_false"), "{text}");
}

#[test]
fn smtlib_text_frontend_handles_set_info_and_decimal_indexed_literals() {
    let script = r#"
        (set-info :smt-lib-version 2.6)
        (set-logic QF_BV)
        (set-info :status unsat)
        (assert (= (bvsmod (_ bv0 4) (_ bv10 4)) (_ bv10 4)))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unsat\n"), "{text}");
}

#[test]
fn smtlib_text_frontend_supports_distinct() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (distinct x x))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unsat\n"), "{text}");
}

#[test]
fn smtlib_text_frontend_expands_define_fun_with_arguments() {
    let script = r#"
        (set-logic QF_BV)
        (define-fun same-low ((a (_ BitVec 4)) (b (_ BitVec 4))) Bool
            (= ((_ extract 1 0) a) ((_ extract 1 0) b)))
        (assert (not (same-low #b0011 #b1011)))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unsat\n"), "{text}");
}

#[test]
fn smtlib_text_frontend_reports_bad_annotation_without_panic() {
    let script = r#"
        (set-logic QF_BV)
        (assert (! :named a))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("error"), "{text}");
}

#[test]
fn smtlib_text_frontend_rejects_malformed_annotation_pairs() {
    for script in [
        "(set-logic QF_BV) (assert (! true :named)) (check-sat)",
        "(set-logic QF_BV) (assert (! true named a)) (check-sat)",
    ] {
        let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("error"), "{text}");
    }
}

#[test]
fn smtlib_text_frontend_accepts_non_named_annotations() {
    let script = "(set-logic QF_BV) (assert (! true :reason ok)) (check-sat)";
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
}

#[test]
fn smtlib_text_frontend_reports_bad_indexed_op_arity_without_panic() {
    let script = r#"
        (set-logic QF_BV)
        (assert ((_ zero_extend 1) #b0 #b1))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("error"), "{text}");
}

#[test]
fn smtlib_yaspar_parser_handles_block_comments_and_quoted_symbols() {
    let script = r#"
        #| block comments are handled by yaspar |#
        (set-logic QF_BV)
        (declare-const |x y| (_ BitVec 2))
        (assert (= |x y| #b11))
        (check-sat)
        (get-value (|x y|))
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("(|x y| #b11)"), "{text}");
}

#[test]
fn smtlib_parser_supports_wide_hex_literals() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 132))
        (assert (= x #x100000000000000000000000000000000))
        (check-sat)
    "#;
    let query = parse_smtlib_script(script).unwrap();
    assert_eq!(query.request.assertion_roots.len(), 1);
}

#[test]
fn smtlib_parser_supports_let_extract_and_assumptions() {
    let script = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (declare-const p Bool)
        (assert (let ((lo ((_ extract 1 0) x))) (= lo #b01)))
        (check-sat-assuming (p))
    "#;
    let query = parse_smtlib_script(script).unwrap();
    assert_eq!(query.request.assumption_roots.len(), 1);
    assert_eq!(query.request.assertion_roots.len(), 1);
}

#[test]
fn smtlib_text_frontend_let_bindings_are_simultaneous() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 1))
        (assert (let ((x #b0) (y x)) (= y #b1)))
        (check-sat)
    "#;
    let output = handle_text_frame(script.as_bytes(), &BinbitBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
}

#[test]
fn smt2_translation_contains_declarations_and_named_assertions() {
    let mut builder = ExprBuilder::new();
    let x = builder.bv_var("x", 4).unwrap();
    let one = builder.bv_const(1, 4).unwrap();
    let eq = builder.bv_eq(x, one).unwrap();
    builder.assert_named("x_is_one", eq).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(1, 0, true, true).unwrap()).unwrap();
    let smt2 = request_to_smt2(&request).unwrap();
    assert!(smt2.script.contains("(declare-fun x () (_ BitVec 4))"));
    assert!(smt2.script.contains(":named x_is_one"));
    assert!(smt2.script.contains("(get-value ( x))"));
    assert!(smt2.script.contains("(get-unsat-core)"));

    let request =
        BinaryRequest::parse(&builder.build_solve_request(2, 123, false, false).unwrap()).unwrap();
    let smt2 = request_to_smt2(&request).unwrap();
    assert!(smt2.script.contains("(set-option :timeout 123)"));
}

struct UnknownBackend;
impl Backend for UnknownBackend {
    fn name(&self) -> &'static str {
        "unknown-test"
    }
    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        Ok(QueryResult::unknown("test unknown"))
    }
}

struct SlowUnknownBackend;
impl Backend for SlowUnknownBackend {
    fn name(&self) -> &'static str {
        "slow-unknown-test"
    }
    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        std::thread::sleep(Duration::from_millis(250));
        Ok(QueryResult::unknown("slow unknown"))
    }
}

struct ImmediateSatBackend;
impl Backend for ImmediateSatBackend {
    fn name(&self) -> &'static str {
        "immediate-sat-test"
    }
    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        Ok(QueryResult::sat(None))
    }
}

struct CancellableSlowBackend {
    observed_cancel: Arc<AtomicBool>,
}
impl Backend for CancellableSlowBackend {
    fn name(&self) -> &'static str {
        "cancellable-slow-test"
    }
    fn handle(&self, _request: &BinaryRequest) -> smt_wire::Result<QueryResult> {
        Ok(QueryResult::unknown("cancellable backend requires context"))
    }
    fn handle_with_context(
        &self,
        _request: &BinaryRequest,
        context: &SolveContext,
    ) -> smt_wire::Result<QueryResult> {
        let start = Instant::now();
        while start.elapsed() < Duration::from_secs(5) {
            if context.is_cancelled() {
                self.observed_cancel.store(true, Ordering::Release);
                return Ok(QueryResult::unknown("cancelled"));
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        Ok(QueryResult::unknown("not cancelled"))
    }
}

#[test]
fn smtlib_text_frontend_does_not_claim_sat_without_requested_model() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 1))
        (check-sat)
        (get-model)
    "#;
    let output = handle_text_frame(script.as_bytes(), &ImmediateSatBackend).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unknown\n"), "{text}");
    assert!(text.contains("omitted requested model"), "{text}");
}

#[test]
fn racing_backend_waits_past_unknown_for_conclusive_result() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(3, 0, false, false).unwrap()).unwrap();
    let racing = RacingBackend::new(vec![Arc::new(UnknownBackend), Arc::new(BinbitBackend)]);
    let result = racing.handle(&request).unwrap();
    assert!(result.is_conclusive());
}

#[test]
fn racing_backend_returns_first_conclusive_without_waiting_for_slow_unknown() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(4, 0, false, false).unwrap()).unwrap();
    let racing = RacingBackend::new(vec![
        Arc::new(SlowUnknownBackend),
        Arc::new(ImmediateSatBackend),
    ]);
    let start = Instant::now();
    let result = racing.handle(&request).unwrap();
    assert!(result.is_conclusive());
    assert!(start.elapsed() < Duration::from_millis(200));
}

#[test]
fn racing_backend_cancels_cooperative_losers_after_winner() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(7, 0, false, false).unwrap()).unwrap();
    let observed_cancel = Arc::new(AtomicBool::new(false));
    let racing = RacingBackend::new(vec![
        Arc::new(CancellableSlowBackend {
            observed_cancel: Arc::clone(&observed_cancel),
        }),
        Arc::new(ImmediateSatBackend),
    ]);
    let result = racing.handle(&request).unwrap();
    assert!(result.is_conclusive());
    for _ in 0..50 {
        if observed_cancel.load(Ordering::Acquire) {
            return;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    assert!(
        observed_cancel.load(Ordering::Acquire),
        "cooperative loser did not observe cancellation"
    );
}

#[test]
fn racing_backend_default_budget_bounds_unbudgeted_requests() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(6, 0, false, false).unwrap()).unwrap();
    let racing = RacingBackend::new(vec![
        Arc::new(SlowUnknownBackend),
        Arc::new(SlowUnknownBackend),
    ])
    .with_default_budget_ms(20);
    let start = Instant::now();
    let result = racing.handle(&request).unwrap();
    assert!(!result.is_conclusive());
    assert!(start.elapsed() < Duration::from_millis(200));
}

#[test]
fn racing_backend_respects_request_budget_while_backends_continue() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(5, 20, false, false).unwrap()).unwrap();
    let racing = RacingBackend::new(vec![
        Arc::new(SlowUnknownBackend),
        Arc::new(SlowUnknownBackend),
    ]);
    let start = Instant::now();
    let result = racing.handle(&request).unwrap();
    assert!(!result.is_conclusive());
    assert!(start.elapsed() < Duration::from_millis(200));
}

#[test]
fn production_backends_observe_pre_cancelled_context() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(11, 0, false, false).unwrap()).unwrap();

    for backend in [
        &BinbitBackend as &dyn Backend,
        &QfbvsmtrsBackend as &dyn Backend,
        &Z3Backend as &dyn Backend,
    ] {
        let cancellation = CancellationToken::new();
        cancellation.cancel();
        let context = SolveContext::new(cancellation);
        let result = backend.handle_with_context(&request, &context).unwrap();
        assert!(
            !result.is_conclusive(),
            "{} returned {result:?}",
            backend.name()
        );
        assert!(
            result
                .message
                .as_deref()
                .unwrap_or_default()
                .contains("cancelled"),
            "{} returned {result:?}",
            backend.name()
        );
    }
}

#[test]
fn z3_backend_extracts_named_unsat_core() {
    let mut builder = ExprBuilder::new();
    let p = builder.bool_var("p").unwrap();
    let not_p = builder.bool_not(p).unwrap();
    builder.assert_named("p_true", p).unwrap();
    builder.assert_named("p_false", not_p).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(10, 0, false, true).unwrap()).unwrap();
    let result = Z3Backend.handle(&request).unwrap();
    let core = result.core.unwrap();
    assert!(core.names.contains(&"p_true".to_owned()));
    assert!(core.names.contains(&"p_false".to_owned()));
}
