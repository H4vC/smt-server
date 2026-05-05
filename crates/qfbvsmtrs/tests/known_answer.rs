use std::path::Path;

use qfbvsmtrs::{solve_smt2, Config, SolveStatus};

#[test]
fn known_answer_fixture_files() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/known");
    let mut paths = std::fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    paths.sort();
    assert!(!paths.is_empty(), "known-answer fixture directory is empty");
    for path in paths {
        let script = std::fs::read_to_string(&path).unwrap();
        let expected = expected_status(&script)
            .unwrap_or_else(|| panic!("{} missing ; EXPECT: sat|unsat", path.display()));
        let result = solve_smt2(&script, &Config::default())
            .unwrap_or_else(|err| panic!("{}: {err}", path.display()));
        assert_eq!(result.status, expected, "{}", path.display());
    }
}

fn expected_status(script: &str) -> Option<SolveStatus> {
    script.lines().find_map(|line| match line.trim() {
        "; EXPECT: sat" => Some(SolveStatus::Sat),
        "; EXPECT: unsat" => Some(SolveStatus::Unsat),
        "; EXPECT: unknown" => Some(SolveStatus::Unknown),
        _ => None,
    })
}

fn check(assertion: &str, expected: SolveStatus) {
    let script = format!("(set-logic QF_BV)\n(assert {assertion})\n(check-sat)\n");
    let result =
        solve_smt2(&script, &Config::default()).unwrap_or_else(|err| panic!("{assertion}: {err}"));
    assert_eq!(result.status, expected, "{assertion}");
}

#[test]
fn known_answer_bv_operations() {
    let sat_cases = [
        "(= (bvnot #b1010) #b0101)",
        "(= (bvand #b1100 #b1010) #b1000)",
        "(= (bvor #b1100 #b1010) #b1110)",
        "(= (bvxor #b1100 #b1010) #b0110)",
        "(= (bvadd #x0f #x01) #x10)",
        "(= (bvsub #x00 #x01) #xff)",
        "(= (bvmul #x0f #x11) #xff)",
        "(= (bvudiv #x07 #x00) #xff)",
        "(= (bvurem #x07 #x00) #x07)",
        "(= (bvsdiv #b1000 #b1111) #b1000)",
        "(= (bvsrem #b1001 #b0011) #b1111)",
        "(= (bvsmod #b1011 #b0010) #b0001)",
        "(= (bvshl #b0011 #b0010) #b1100)",
        "(= (bvlshr #b1000 #b0010) #b0010)",
        "(= (bvashr #b1000 #b0010) #b1110)",
        "(= (concat #b10 #b011) #b10011)",
        "(= ((_ extract 3 1) #b1101) #b110)",
        "(= ((_ zero_extend 3) #b101) #b000101)",
        "(= ((_ sign_extend 3) #b101) #b111101)",
        "(= ((_ repeat 3) #b10) #b101010)",
        "(= ((_ rotate_left 1) #b1001) #b0011)",
        "(= ((_ rotate_right 1) #b1001) #b1100)",
        "(bvult #x0f #x10)",
        "(bvule #x10 #x10)",
        "(bvugt #x10 #x0f)",
        "(bvuge #x10 #x10)",
        "(bvslt #b1000 #b0111)",
        "(bvsle #b1000 #b1000)",
        "(bvsgt #b0111 #b1000)",
        "(bvsge #b1000 #b1000)",
        "(bvuaddo #b1111 #b0001)",
        "(not (bvuaddo #x01 #x01))",
        "(bvsaddo #b0111 #b0001)",
        "(bvusubo #x00 #x01)",
        "(bvssubo #b1000 #b0001)",
        "(bvumulo #x10 #x10)",
        "(bvsmulo #b0100 #b0010)",
        "(bvnego #b1000)",
        "(bvsdivo #b1000 #b1111)",
        "(= (ite true #x12 #x34) #x12)",
        "(= (let ((x #x0f)) (bvadd x #x01)) #x10)",
        "(= (_ bv340282366920938463463374607431768211455 128) #xffffffffffffffffffffffffffffffff)",
    ];
    for assertion in sat_cases {
        check(assertion, SolveStatus::Sat);
        check(&format!("(not {assertion})"), SolveStatus::Unsat);
    }
}

#[test]
fn known_answer_width_one_and_boolean_edges() {
    let cases = [
        "(= (bvadd #b1 #b1) #b0)",
        "(= (bvmul #b1 #b1) #b1)",
        "(= (bvudiv #b0 #b0) #b1)",
        "(= (bvurem #b1 #b0) #b1)",
        "(= ((_ sign_extend 7) #b1) #xff)",
        "(= ((_ zero_extend 7) #b1) #x01)",
        "(= (ite false #b0 #b1) #b1)",
    ];
    for assertion in cases {
        check(assertion, SolveStatus::Sat);
    }
}
