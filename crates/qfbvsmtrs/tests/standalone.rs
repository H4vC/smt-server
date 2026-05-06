use std::path::PathBuf;
use std::process::Command as ProcessCommand;
use std::time::Duration;

use qfbvsmtrs::{
    format_smt2_response, parse_smt2, solve_smt2, Builder, Command, Config, SatBackendKind,
    ScalarValue, SolveResult, SolveStatus, Solver,
};

#[test]
fn standalone_cli_supports_budget_backend_and_input_bound() {
    let exe = env!("CARGO_BIN_EXE_qfbvsmtrs");
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("known")
        .join("simple_unsat.smt2");
    let output = ProcessCommand::new(exe)
        .args([
            "--budget-ms",
            "1000",
            "--sat-backend",
            "dpll",
            "--shortcut-mode",
            "disabled",
        ])
        .arg(&fixture)
        .output()
        .expect("run qfbvsmtrs CLI");
    assert!(output.status.success(), "{output:?}");
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "unsat\n");

    let output = ProcessCommand::new(exe)
        .args(["--max-input-bytes", "1"])
        .arg(&fixture)
        .output()
        .expect("run qfbvsmtrs CLI input-bound smoke");
    assert!(!output.status.success(), "{output:?}");
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("input exceeds"), "{stderr}");
}

#[test]
fn all_sat_backends_solve_basic_sat_and_unsat() {
    let sat = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= (bvadd x #x1) #x3))
(check-sat)
(get-model)
"#;
    let unsat = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #x1))
(assert (= x #x2))
(check-sat)
"#;
    for backend in [
        SatBackendKind::Splr,
        SatBackendKind::Varisat,
        SatBackendKind::Dpll,
    ] {
        let config = Config::default().with_sat_backend(backend);
        let sat_result = solve_smt2(sat, &config).unwrap();
        assert_eq!(sat_result.status, SolveStatus::Sat, "{backend:?} SAT");
        assert_eq!(
            sat_result.model.unwrap().get("x"),
            Some(&ScalarValue::Bv {
                width: 4,
                bytes: vec![2]
            }),
            "{backend:?} model"
        );

        let unsat_result = solve_smt2(unsat, &config).unwrap();
        assert_eq!(unsat_result.status, SolveStatus::Unsat, "{backend:?} UNSAT");
    }
}

#[test]
fn varisat_reports_unknown_for_budgeted_solves() {
    let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #x1))
(check-sat)
"#;
    let config = Config::default()
        .with_sat_backend(SatBackendKind::Varisat)
        .with_budget(Some(Duration::from_millis(10)));
    let result = solve_smt2(script, &config).unwrap();
    assert_eq!(result.status, SolveStatus::Unknown);
}

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
fn standalone_formatter_does_not_claim_missing_requested_artifacts() {
    let model_query = parse_smt2(
        r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(check-sat)
(get-model)
"#,
    )
    .unwrap();
    let text = format_smt2_response(&model_query, &SolveResult::sat(None));
    assert!(text.starts_with("unknown\n"), "{text}");
    assert!(text.contains("requested model"), "{text}");

    let core_query = parse_smt2(
        r#"
(set-logic QF_BV)
(declare-const p Bool)
(assert (! p :named p))
(check-sat)
(get-unsat-core)
"#,
    )
    .unwrap();
    let text = format_smt2_response(&core_query, &SolveResult::unsat());
    assert!(text.starts_with("unknown\n"), "{text}");
    assert!(text.contains("requested unsat core"), "{text}");

    let text = format_smt2_response(&model_query, &SolveResult::unknown("budget exhausted"));
    assert!(text.contains("budget exhausted"), "{text}");
}

#[test]
fn smt2_frontend_rejects_malformed_constructs_without_panic() {
    assert!(parse_smt2("(set-logic QF_BV) (assert (! :named a)) (check-sat)").is_err());
    assert!(parse_smt2("(set-logic QF_BV) (assert (! true :named)) (check-sat)").is_err());
    assert!(parse_smt2("(set-logic QF_BV) (assert (! true named a)) (check-sat)").is_err());
    assert!(parse_smt2("(set-logic QF_BV) (assert (! true :foo bar)) (check-sat)").is_ok());
    assert!(parse_smt2("(set-logic QF_BV) (assert ((_ extract 0 1) #b0)) (check-sat)").is_err());
    assert!(parse_smt2(
        "(set-logic QF_BV) (define-fun f ((x Bool) (x Bool)) Bool x) (assert true) (check-sat)"
    )
    .is_err());
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
