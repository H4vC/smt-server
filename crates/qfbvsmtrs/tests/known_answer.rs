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
        "(= (bvand #b1100 #b1010 #b0111) #b0000)",
        "(= (bvnand #b1100 #b1010) #b0111)",
        "(= (bvor #b1100 #b1010) #b1110)",
        "(= (bvor #b1000 #b0100 #b0010) #b1110)",
        "(= (bvnor #b1100 #b1010) #b0001)",
        "(= (bvxor #b1100 #b1010) #b0110)",
        "(= (bvxnor #b1100 #b1010) #b1001)",
        "(= (bvcomp #b1100 #b1100) #b1)",
        "(= (bvadd #x0f #x01 #x01) #x11)",
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
        "(= ((_ extract 5 2) (concat #b101 #b110)) #b1011)",
        "(= (concat ((_ extract 7 4) #xab) ((_ extract 3 0) #xab)) #xab)",
        "(= ((_ zero_extend 3) #b101) #b000101)",
        "(= ((_ zero_extend 24) #x01) #x00000001)",
        "(= ((_ sign_extend 3) #b101) #b111101)",
        "(= ((_ sign_extend 24) #x80) #xffffff80)",
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
fn known_answer_associative_commutative_rewrites() {
    let script = "
        (set-logic QF_BV)
        (declare-fun s () (_ BitVec 32))
        (declare-fun t () (_ BitVec 32))
        (assert (not (=
            (bvadd t (bvadd s (bvmul s s)))
            (bvadd s (bvadd t (bvmul s s))))))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);

    let polynomial_script = "
        (set-logic QF_BV)
        (declare-fun s () (_ BitVec 32))
        (declare-fun t () (_ BitVec 32))
        (assert (not (=
            (bvmul t (bvadd s (bvmul s s)))
            (bvmul s (bvadd t (bvmul s t))))))
        (check-sat)
    ";
    let result = solve_smt2(polynomial_script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn known_answer_shifted_add_factorization_rewrite() {
    let script = "
        (set-logic QF_BV)
        (declare-fun s () (_ BitVec 32))
        (declare-fun t () (_ BitVec 32))
        (assert (not (=
            (bvmul t (bvadd s (bvshl s s)))
            (bvmul s (bvadd t (bvshl t s))))))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn known_answer_shifted_product_rewrite() {
    let script = "
        (set-logic QF_BV)
        (declare-fun s () (_ BitVec 32))
        (declare-fun t () (_ BitVec 32))
        (assert (not (=
            (bvmul t (bvshl s (bvneg s)))
            (bvmul s (bvshl t (bvneg s))))))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn known_answer_disjoint_bit_add_simplification() {
    let script = "
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (declare-fun d () (_ BitVec 8))
        (assert (not (=
            (bvadd (bvshl ((_ zero_extend 24) a) #x00000018) ((_ zero_extend 24) b))
            (bvor (bvshl ((_ zero_extend 24) a) #x00000018) ((_ zero_extend 24) b)))) )
        (assert (not (=
            (bvand (bvshl ((_ zero_extend 248) c) (_ bv248 256)) ((_ zero_extend 248) d))
            (_ bv0 256))))
        (assert (not (=
            (bvxor (bvshl ((_ zero_extend 248) c) (_ bv248 256)) ((_ zero_extend 248) d))
            (bvor (bvshl ((_ zero_extend 248) c) (_ bv248 256)) ((_ zero_extend 248) d)))))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn known_answer_left_then_right_shift_identity() {
    let script = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (not (=
            (bvlshr (bvshl x #x03) #x05)
            ((_ zero_extend 5) ((_ extract 4 2) x)))))
        (assert (not (=
            (bvlshr (bvshl x #x05) #x02)
            (bvshl ((_ zero_extend 5) ((_ extract 2 0) x)) #x03))))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
}

#[test]
fn known_answer_noetzli_simplification_identities() {
    for assertion in [
        "(= (bvmul t (bvadd (bvlshr t t) s)) (bvmul s t))",
        "(= (bvand s (bvmul t (bvneg t))) (bvand s (bvneg (bvmul t t))))",
        "(= (bvmul s (bvor t (bvand s t))) (bvmul s t))",
        "(= (bvmul s (bvor t (bvshl t t))) (bvmul s (bvadd t (bvshl t t))))",
        "(= (bvmul (bvmul s t) (bvshl t s)) (bvmul s (bvmul t (bvshl t s))))",
        "(= (bvlshr (bvlshr s (bvmul s t)) t) (bvlshr (bvlshr s t) (bvmul s t)))",
    ] {
        let script = format!(
            "
            (set-logic QF_BV)
            (declare-fun s () (_ BitVec 32))
            (declare-fun t () (_ BitVec 32))
            (assert (not {assertion}))
            (check-sat)
            "
        );
        let result = solve_smt2(&script, &Config::default()).unwrap();
        assert_eq!(result.status, SolveStatus::Unsat, "{assertion}");
    }
}

#[test]
fn known_answer_extension_and_one_bit_ite_simplifications() {
    let zext_out_of_range = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= ((_ zero_extend 8) x) #x0100))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(zext_out_of_range, &Config::default())
            .unwrap()
            .status,
        SolveStatus::Unsat
    );

    let zext_cmp_tautology = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (not (bvult ((_ zero_extend 24) x) (_ bv300 32))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(zext_cmp_tautology, &Config::default())
            .unwrap()
            .status,
        SolveStatus::Unsat
    );

    let one_bit_ite = "
        (set-logic QF_BV)
        (declare-fun p () Bool)
        (assert p)
        (assert (= (ite p #b1 #b0) #b0))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(one_bit_ite, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_small_explicit_assignment_sat_witness() {
    let script = "
        (set-logic QF_BV)
        (declare-fun s () (_ BitVec 32))
        (declare-fun t () (_ BitVec 32))
        (assert (not (= (bvmul t (bvlshr s (bvshl t s)))
                        (bvmul s (bvlshr t (bvshl t s))))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Sat
    );
}

#[test]
fn known_answer_affine_byte_sat_witness() {
    let script = "
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (assert (= (_ bv65636 32)
            (bvadd (bvmul ((_ zero_extend 24) a) (_ bv65599 32))
                   (bvadd (bvmul ((_ zero_extend 24) b) (_ bv17 32))
                          ((_ zero_extend 24) c)))))
        (assert (bvult ((_ zero_extend 24) a) (_ bv97 32)))
        (assert (bvult ((_ zero_extend 24) b) (_ bv97 32)))
        (assert (bvult ((_ zero_extend 24) c) (_ bv97 32)))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Sat
    );

    let packed = "
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 8))
        (declare-fun b () (_ BitVec 8))
        (declare-fun c () (_ BitVec 8))
        (declare-fun d () (_ BitVec 8))
        (assert (= (_ bv67305985 32)
            (bvor (bvshl ((_ zero_extend 24) d) (_ bv24 32))
              (bvor (bvshl ((_ zero_extend 24) c) (_ bv16 32))
                (bvor (bvshl ((_ zero_extend 24) b) (_ bv8 32))
                      ((_ zero_extend 24) a))))))
        (assert (bvsge a (_ bv0 8)))
        (assert (bvsge b (_ bv0 8)))
        (assert (bvsge c (_ bv0 8)))
        (assert (bvsge d (_ bv0 8)))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(packed, &Config::default()).unwrap().status,
        SolveStatus::Sat
    );
}

#[test]
fn known_answer_sparse_constant_multiplication_blasting() {
    let times_two = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (assert (not (= (bvmul x (_ bv2 16)) (bvshl x (_ bv1 16)))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(times_two, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );

    let times_minus_one = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (assert (not (= (bvmul x #xffff) (bvneg x))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(times_minus_one, &Config::default())
            .unwrap()
            .status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_constant_assignment_sat_shortcut() {
    let script = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 1024))
        (declare-fun y () (_ BitVec 1024))
        (declare-fun z () (_ BitVec 1024))
        (assert (not (= (bvudiv x y) (bvand z y))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Sat
    );
}

#[test]
fn known_answer_simple_processor_equivalence_shortcut() {
    let script = "
        (set-logic QF_BV)
        (declare-fun opcode () (_ BitVec 8))
        (declare-fun operator1 () (_ BitVec 4))
        (declare-fun operator2 () (_ BitVec 4))
        (declare-fun opr1_1 () (_ BitVec 4))
        (declare-fun op1_1 () (_ BitVec 4))
        (declare-fun opr2_1 () (_ BitVec 4))
        (declare-fun op2_1 () (_ BitVec 4))
        (declare-fun decode_1 () (_ BitVec 9))
        (declare-fun dec_func_1 () (_ BitVec 1))
        (declare-fun deci_func_1 () (_ BitVec 1))
        (declare-fun func_1 () (_ BitVec 1))
        (declare-fun out_1 () (_ BitVec 4))
        (declare-fun mode_1 () (_ BitVec 1))
        (declare-fun opr1_2 () (_ BitVec 4))
        (declare-fun op1_2 () (_ BitVec 4))
        (declare-fun opr2_2 () (_ BitVec 4))
        (declare-fun op2_2 () (_ BitVec 4))
        (declare-fun decode_2 () (_ BitVec 9))
        (declare-fun dec_func_2 () (_ BitVec 1))
        (declare-fun deci_func_2 () (_ BitVec 1))
        (declare-fun func_2 () (_ BitVec 1))
        (declare-fun out_2 () (_ BitVec 4))
        (declare-fun mode_2 () (_ BitVec 1))
        (assert
          (and
            (= opr1_1 operator1)
            (ite (= opcode (_ bv136 8)) (and (= dec_func_1 #b1) (= opr2_1 operator2))
              (ite (= opcode (_ bv137 8)) (and (= dec_func_1 #b0) (= opr2_1 operator2))
                (ite (= opcode (_ bv138 8)) (and (= dec_func_1 #b1) (= opr2_1 #x1))
                  (and (= dec_func_1 #b0) (= opr2_1 #x1)))))
            (ite (= opcode (_ bv136 8)) (and (= deci_func_1 #b1) (= opr2_1 operator2))
              (ite (= opcode (_ bv137 8)) (and (= deci_func_1 #b0) (= opr2_1 operator2))
                (ite (= opcode (_ bv138 8)) (and (= deci_func_1 #b1) (= opr2_1 #x1))
                  (and (= deci_func_1 #b0) (= opr2_1 #x1)))))
            (ite (= mode_1 #b0)
              (= decode_1 (concat (concat dec_func_1 opr1_1) opr2_1))
              (= decode_1 (concat (concat deci_func_1 opr2_1) opr1_1)))
            (ite (= mode_1 #b0)
              (and (= func_1 ((_ extract 8 8) decode_1)) (= op1_1 ((_ extract 7 4) decode_1)) (= op2_1 ((_ extract 3 0) decode_1)))
              (and (= func_1 ((_ extract 8 8) decode_1)) (= op2_1 ((_ extract 7 4) decode_1)) (= op1_1 ((_ extract 3 0) decode_1))))
            (ite (= func_1 #b1) (= out_1 (bvadd op1_1 op2_1)) (= out_1 (bvor op1_1 op2_1)))
            (= opr1_2 operator1)
            (ite (= opcode (_ bv136 8)) (and (= dec_func_2 #b1) (= opr2_2 operator2))
              (ite (= opcode (_ bv137 8)) (and (= dec_func_2 #b0) (= opr2_2 operator2))
                (ite (= opcode (_ bv138 8)) (and (= dec_func_2 #b1) (= opr2_2 #x1))
                  (and (= dec_func_2 #b0) (= opr2_2 #x1)))))
            (ite (= opcode (_ bv136 8)) (and (= deci_func_2 #b1) (= opr2_2 operator2))
              (ite (= opcode (_ bv137 8)) (and (= deci_func_2 #b0) (= opr2_2 operator2))
                (ite (= opcode (_ bv138 8)) (and (= deci_func_2 #b1) (= opr2_2 #x1))
                  (and (= deci_func_2 #b0) (= opr2_2 #x1)))))
            (ite (= mode_2 #b0)
              (= decode_2 (concat (concat opr1_2 dec_func_2) opr2_2))
              (= decode_2 (concat (concat opr2_2 deci_func_2) opr1_2)))
            (ite (= mode_2 #b0)
              (and (= op1_2 ((_ extract 8 5) decode_2)) (= func_2 ((_ extract 4 4) decode_2)) (= op2_2 ((_ extract 3 0) decode_2)))
              (and (= op2_2 ((_ extract 8 5) decode_2)) (= func_2 ((_ extract 4 4) decode_2)) (= op1_2 ((_ extract 3 0) decode_2))))
            (ite (= func_2 #b1) (= out_2 (bvadd op1_2 op2_2)) (= out_2 (bvor op1_2 op2_2)))
            (and (= mode_1 mode_2) (not (= out_1 out_2)))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_synchronized_lfsr_shortcut() {
    let step = |from: &str, to: &str, reset: &str| {
        format!(
            "(ite {reset} (= {to} #b0000) (= {to} \
             (concat ((_ extract 2 0) {from}) \
                     (bvxor ((_ extract 3 3) {from}) ((_ extract 2 2) {from})))))",
        )
    };
    let script = format!(
        "
        (set-logic QF_BV)
        (declare-fun reset_0 () Bool)
        (declare-fun reset_1 () Bool)
        (declare-fun q1_0 () (_ BitVec 4))
        (declare-fun q1_1 () (_ BitVec 4))
        (declare-fun q1_2 () (_ BitVec 4))
        (declare-fun q2_0 () (_ BitVec 4))
        (declare-fun q2_1 () (_ BitVec 4))
        (declare-fun q2_2 () (_ BitVec 4))
        (declare-fun q3_0 () (_ BitVec 4))
        (declare-fun q3_1 () (_ BitVec 4))
        (declare-fun q3_2 () (_ BitVec 4))
        (assert (and
            {q10}
            {q11}
            {q20}
            {q21}
            {q30}
            {q31}
            (not (= q1_0 q2_0))
            (not (= q1_0 q3_0))
            (not (= q2_0 q3_0))
            (= (or (= q1_2 q2_2) (= q1_2 q3_2) (= q2_2 q3_2))
               (and (not reset_0) (not reset_1)))))
        (check-sat)
        ",
        q10 = step("q1_0", "q1_1", "reset_0"),
        q11 = step("q1_1", "q1_2", "reset_1"),
        q20 = step("q2_0", "q2_1", "reset_0"),
        q21 = step("q2_1", "q2_2", "reset_1"),
        q30 = step("q3_0", "q3_1", "reset_0"),
        q31 = step("q3_1", "q3_2", "reset_1"),
    );
    assert_eq!(
        solve_smt2(&script, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_extensional_candidate_shortcut() {
    let script = "
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 32))
        (declare-fun d () (_ BitVec 8))
        (declare-fun v1 () (_ BitVec 32))
        (declare-fun v2 () (_ BitVec 32))
        (assert (and
            (not (= ((_ extract 23 16) v1) ((_ extract 15 8) v1)))
            (not (= ((_ extract 23 16) v2) ((_ extract 15 8) v2)))
            (or
                (and
                    (= ((_ extract 31 8) a) (concat ((_ extract 31 16) v1) d))
                    (= ((_ extract 23 0) a) (concat d ((_ extract 15 0) v1))))
                (and
                    (= ((_ extract 31 8) a) (concat ((_ extract 31 16) v2) d))
                    (= ((_ extract 23 0) a) (concat d ((_ extract 15 0) v2)))))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_log_slicing_shift_shortcut() {
    let script = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (declare-fun amount () (_ BitVec 4))
        (declare-fun result () (_ BitVec 4))
        (assert (= result (bvshl x amount)))
        (declare-fun sx0 () (_ BitVec 4))
        (assert (= sx0 x))
        (declare-fun sh1 () (_ BitVec 4))
        (assert (= ((_ extract 2 0) sx0) ((_ extract 3 1) sh1)))
        (assert (= #b0 ((_ extract 0 0) sh1)))
        (declare-fun m1 () (_ BitVec 4))
        (assert (= m1 (concat (concat ((_ extract 0 0) amount) ((_ extract 0 0) amount))
                              (concat ((_ extract 0 0) amount) ((_ extract 0 0) amount)))))
        (declare-fun sx1 () (_ BitVec 4))
        (assert (= sx1 (bvor (bvand m1 sh1) (bvand (bvnot m1) sx0))))
        (declare-fun sh2 () (_ BitVec 4))
        (assert (= ((_ extract 1 0) sx1) ((_ extract 3 2) sh2)))
        (assert (= #b00 ((_ extract 1 0) sh2)))
        (declare-fun m2 () (_ BitVec 4))
        (assert (= m2 (concat (concat ((_ extract 1 1) amount) ((_ extract 1 1) amount))
                              (concat ((_ extract 1 1) amount) ((_ extract 1 1) amount)))))
        (declare-fun sx2 () (_ BitVec 4))
        (assert (= sx2 (bvor (bvand m2 sh2) (bvand (bvnot m2) sx1))))
        (declare-fun x0 () (_ BitVec 4))
        (declare-fun y0 () (_ BitVec 4))
        (assert (= x0 amount))
        (assert (= y0 #x4))
        (declare-fun c1 () (_ BitVec 1))
        (assert (= (= c1 #b1) (= ((_ extract 3 2) x0) ((_ extract 3 2) y0))))
        (declare-fun cm1 () (_ BitVec 2))
        (assert (= cm1 (concat c1 c1)))
        (declare-fun cx1 () (_ BitVec 2))
        (declare-fun cy1 () (_ BitVec 2))
        (assert (= cx1 (bvor (bvand cm1 ((_ extract 1 0) x0)) (bvand (bvnot cm1) ((_ extract 3 2) x0)))))
        (assert (= cy1 (bvor (bvand cm1 ((_ extract 1 0) y0)) (bvand (bvnot cm1) ((_ extract 3 2) y0)))))
        (declare-fun c2 () (_ BitVec 1))
        (assert (= (= c2 #b1) (= ((_ extract 1 1) cx1) ((_ extract 1 1) cy1))))
        (declare-fun cx2 () (_ BitVec 1))
        (declare-fun cy2 () (_ BitVec 1))
        (assert (= cx2 (bvor (bvand c2 ((_ extract 0 0) cx1)) (bvand (bvnot c2) ((_ extract 1 1) cx1)))))
        (assert (= cy2 (bvor (bvand c2 ((_ extract 0 0) cy1)) (bvand (bvnot c2) ((_ extract 1 1) cy1)))))
        (declare-fun lt () (_ BitVec 1))
        (assert (= lt (bvand (bvnot cx2) cy2)))
        (declare-fun valid () (_ BitVec 4))
        (assert (= valid (concat (concat lt lt) (concat lt lt))))
        (assert (not (= result (bvor (bvand valid sx2) (bvand (bvnot valid) #x0)))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_log_slicing_comparison_shortcut() {
    let script = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 3))
        (declare-fun y () (_ BitVec 3))
        (declare-fun result () Bool)
        (assert (= result (bvult x y)))
        (declare-fun x0 () (_ BitVec 4))
        (declare-fun y0 () (_ BitVec 4))
        (assert (= #b0 ((_ extract 3 3) x0)))
        (assert (= x ((_ extract 2 0) x0)))
        (assert (= #b0 ((_ extract 3 3) y0)))
        (assert (= y ((_ extract 2 0) y0)))
        (declare-fun c1 () (_ BitVec 1))
        (assert (= (= c1 #b1) (= ((_ extract 3 2) x0) ((_ extract 3 2) y0))))
        (declare-fun mx1 () (_ BitVec 2))
        (declare-fun my1 () (_ BitVec 2))
        (assert (= c1 ((_ extract 1 1) mx1)))
        (assert (= c1 ((_ extract 0 0) mx1)))
        (assert (= c1 ((_ extract 1 1) my1)))
        (assert (= c1 ((_ extract 0 0) my1)))
        (declare-fun x1 () (_ BitVec 2))
        (declare-fun y1 () (_ BitVec 2))
        (assert (= x1 (bvor (bvand mx1 ((_ extract 1 0) x0)) (bvand (bvnot mx1) ((_ extract 3 2) x0)))))
        (assert (= y1 (bvor (bvand my1 ((_ extract 1 0) y0)) (bvand (bvnot my1) ((_ extract 3 2) y0)))))
        (declare-fun c2 () (_ BitVec 1))
        (assert (= (= c2 #b1) (= ((_ extract 1 1) x1) ((_ extract 1 1) y1))))
        (declare-fun mx2 () (_ BitVec 1))
        (declare-fun my2 () (_ BitVec 1))
        (assert (= mx2 c2))
        (assert (= my2 c2))
        (declare-fun x2 () (_ BitVec 1))
        (declare-fun y2 () (_ BitVec 1))
        (assert (= x2 (bvor (bvand mx2 ((_ extract 0 0) x1)) (bvand (bvnot mx2) ((_ extract 1 1) x1)))))
        (assert (= y2 (bvor (bvand my2 ((_ extract 0 0) y1)) (bvand (bvnot my2) ((_ extract 1 1) y1)))))
        (assert (not (= result (= (bvand (bvnot x2) y2) #b1))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(script, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_log_slicing_adder_shortcuts() {
    let add = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (declare-fun y () (_ BitVec 16))
        (declare-fun r () (_ BitVec 16))
        (assert (= r (bvadd x y)))
        (declare-fun sum () (_ BitVec 16))
        (declare-fun cin () (_ BitVec 16))
        (declare-fun cout () (_ BitVec 16))
        (assert (= sum (bvxor (bvxor x y) cin)))
        (assert (= cout (bvor (bvor (bvand x y) (bvand x cin)) (bvand y cin))))
        (declare-fun shifted () (_ BitVec 16))
        (assert (= ((_ extract 14 0) cout) ((_ extract 15 1) shifted)))
        (assert (= #b0 ((_ extract 0 0) shifted)))
        (assert (= cin shifted))
        (assert (not (= r sum)))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(add, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );

    let sub = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (declare-fun y () (_ BitVec 16))
        (declare-fun r () (_ BitVec 16))
        (assert (= r (bvsub x y)))
        (declare-fun neg_y () (_ BitVec 16))
        (declare-fun cin1 () (_ BitVec 16))
        (declare-fun cout1 () (_ BitVec 16))
        (assert (= neg_y (bvxor (bvxor (bvnot y) (_ bv1 16)) cin1)))
        (assert (= cout1 (bvor (bvor (bvand (bvnot y) (_ bv1 16)) (bvand (bvnot y) cin1)) (bvand (_ bv1 16) cin1))))
        (declare-fun shifted1 () (_ BitVec 16))
        (assert (= ((_ extract 14 0) cout1) ((_ extract 15 1) shifted1)))
        (assert (= #b0 ((_ extract 0 0) shifted1)))
        (assert (= cin1 shifted1))
        (declare-fun sum () (_ BitVec 16))
        (declare-fun cin2 () (_ BitVec 16))
        (declare-fun cout2 () (_ BitVec 16))
        (assert (= sum (bvxor (bvxor x neg_y) cin2)))
        (assert (= cout2 (bvor (bvor (bvand x neg_y) (bvand x cin2)) (bvand neg_y cin2))))
        (declare-fun shifted2 () (_ BitVec 16))
        (assert (= ((_ extract 14 0) cout2) ((_ extract 15 1) shifted2)))
        (assert (= #b0 ((_ extract 0 0) shifted2)))
        (assert (= cin2 shifted2))
        (assert (not (= r sum)))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(sub, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_large_width_pattern_shortcuts() {
    let shift1add = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 10000))
        (declare-fun y () (_ BitVec 10000))
        (declare-fun z () (_ BitVec 10000))
        (assert (= z (bvadd x y)))
        (assert (= z (bvshl x (_ bv1 10000))))
        (assert (distinct x y))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(shift1add, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );

    let power2sum = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 5500))
        (declare-fun y () (_ BitVec 5500))
        (declare-fun z () (_ BitVec 5500))
        (assert (= z (bvadd x y)))
        (assert (distinct x y))
        (assert (and (distinct x (_ bv0 5500)) (= (bvand x (bvsub x (_ bv1 5500))) (_ bv0 5500))))
        (assert (and (distinct y (_ bv0 5500)) (= (bvand y (bvsub y (_ bv1 5500))) (_ bv0 5500))))
        (assert (and (distinct z (_ bv0 5500)) (= (bvand z (bvsub z (_ bv1 5500))) (_ bv0 5500))))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(power2sum, &Config::default()).unwrap().status,
        SolveStatus::Unsat
    );

    let wrap_sat = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 20000))
        (declare-fun y () (_ BitVec 20000))
        (assert (bvuge x y))
        (assert (bvule (bvadd x (_ bv1 20000)) y))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(wrap_sat, &Config::default()).unwrap().status,
        SolveStatus::Sat
    );

    let guarded_multiply_overflow = "
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 32))
        (declare-fun b () (_ BitVec 32))
        (assert (not (= ((_ extract 63 32)
            (bvmul ((_ zero_extend 32) a) ((_ zero_extend 32) b))) #x00000000)))
        (assert (bvuge (bvudiv #xffffffff a) b))
        (check-sat)
    ";
    assert_eq!(
        solve_smt2(guarded_multiply_overflow, &Config::default())
            .unwrap()
            .status,
        SolveStatus::Unsat
    );
}

#[test]
fn known_answer_unsigned_successor_order_contradiction() {
    let script = "
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 20000))
        (declare-fun y () (_ BitVec 20000))
        (assert (bvult x y))
        (assert (bvugt (bvadd x (_ bv1 20000)) y))
        (check-sat)
    ";
    let result = solve_smt2(script, &Config::default()).unwrap();
    assert_eq!(result.status, SolveStatus::Unsat);
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
