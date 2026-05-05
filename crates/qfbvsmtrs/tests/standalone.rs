use qfbvsmtrs::{solve_smt2, Builder, Command, Config, ScalarValue, SolveStatus, Solver};

#[test]
fn solves_simple_sat_with_model() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x2a))
(check-sat)
(get-model)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Sat);
    let model = result.model.unwrap();
    assert_eq!(
        model.get("x"),
        Some(&ScalarValue::Bv {
            width: 8,
            bytes: vec![0x2a]
        })
    );
}

#[test]
fn supports_push_pop_in_standalone_script() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(push 1)
(assert (= x #x1))
(pop 1)
(assert (= x #x2))
(check-sat)
(get-model)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Sat);
    assert_eq!(
        result.model.unwrap().get("x"),
        Some(&ScalarValue::Bv {
            width: 4,
            bytes: vec![2]
        })
    );
}

#[test]
fn solves_simple_unsat() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #x1))
(assert (= x #x2))
(check-sat)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn extracts_named_unsat_core() {
    let script = r#"
(set-logic QF_BV)
(declare-const p Bool)
(assert (! p :named p-true))
(assert (! (not p) :named p-false))
(check-sat)
(get-unsat-core)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
    assert_eq!(
        result.core.unwrap(),
        vec!["p-true".to_owned(), "p-false".to_owned()]
    );
}

#[test]
fn solves_bvadd_constraint() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= (bvadd x #x1) #x3))
(check-sat)
(get-model)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Sat);
    let model = result.model.unwrap();
    assert_eq!(
        model.get("x"),
        Some(&ScalarValue::Bv {
            width: 4,
            bytes: vec![0x2]
        })
    );
}

#[test]
fn optimizes_unsigned_target() {
    let mut builder = Builder::new();
    let x = builder.bv_var("x", 4).unwrap();
    let three = builder.bv_const(3, 4).unwrap();
    let ge = builder.bv_uge(x, three).unwrap();
    builder.assert(ge).unwrap();
    builder
        .set_optimization(Command::Minimize, x, false)
        .unwrap();
    let query = builder.finish().unwrap();
    let result = Solver::default().solve(&query).unwrap();
    assert_eq!(result.status, SolveStatus::Sat);
    assert_eq!(
        result.optimum,
        Some(ScalarValue::Bv {
            width: 4,
            bytes: vec![3]
        })
    );
}

#[test]
fn handles_unsigned_division_by_zero_semantics() {
    let script = r#"
(set-logic QF_BV)
(assert (= (bvudiv #x5 #x0) #xf))
(assert (= (bvurem #x5 #x0) #x5))
(check-sat)
"#;
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Sat);
}
