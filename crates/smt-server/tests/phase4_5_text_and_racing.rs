use std::sync::Arc;

use smt_server::{
    handle_text_frame, parse_smtlib_script, request_to_smt2, Backend, ExhaustiveBackend,
    QueryResult, RacingBackend,
};
use smt_wire::{BinaryRequest, ExprBuilder};

#[test]
fn smtlib_text_frontend_solves_sat_and_formats_model() {
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 2))
        (assert (= x #b01))
        (check-sat)
        (get-model)
    "#;
    let output = handle_text_frame(script.as_bytes(), &ExhaustiveBackend::default()).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("sat\n"), "{text}");
    assert!(text.contains("define-fun x"), "{text}");
    assert!(text.contains("#b01"), "{text}");
}

#[test]
fn smtlib_text_frontend_rejects_incremental_commands() {
    let script = "(set-logic QF_BV) (push) (check-sat)";
    let output = handle_text_frame(script.as_bytes(), &ExhaustiveBackend::default()).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.contains("error"), "{text}");
    assert!(text.contains("push"), "{text}");
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
    let output = handle_text_frame(script.as_bytes(), &ExhaustiveBackend::default()).unwrap();
    let text = String::from_utf8(output).unwrap();
    assert!(text.starts_with("unsat\n"), "{text}");
    assert!(text.contains("p_true"), "{text}");
    assert!(text.contains("p_false"), "{text}");
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

#[test]
fn racing_backend_waits_past_unknown_for_conclusive_result() {
    let mut builder = ExprBuilder::new();
    let t = builder.bool_true().unwrap();
    builder.assert(t).unwrap();
    let request =
        BinaryRequest::parse(&builder.build_solve_request(3, 0, false, false).unwrap()).unwrap();
    let racing = RacingBackend::new(vec![
        Arc::new(UnknownBackend),
        Arc::new(ExhaustiveBackend::default()),
    ]);
    let result = racing.handle(&request).unwrap();
    assert!(result.is_conclusive());
}
