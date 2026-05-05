use qfbvsmtrs::cnf;
use qfbvsmtrs::config::SatBackendKind;
use qfbvsmtrs::gates::{GateArena, GateId};
use qfbvsmtrs::sat::{solve_cnf, SatResult};

fn force(gate: GateId, value: bool) -> i32 {
    let lit = cnf::lit(gate);
    if value {
        lit
    } else {
        -lit
    }
}

fn assert_cnf_agrees(gates: &GateArena, inputs: &[(GateId, bool)], output: GateId, expected: bool) {
    for backend in [
        SatBackendKind::Splr,
        SatBackendKind::Varisat,
        SatBackendKind::Dpll,
    ] {
        let base = cnf::encode(gates, gates.true_gate());

        let mut clauses = base.clauses.clone();
        for &(gate, value) in inputs {
            clauses.push(vec![force(gate, value)]);
        }
        clauses.push(vec![force(output, expected)]);
        assert!(
            matches!(
                solve_cnf(backend, base.num_vars, clauses, &[], None),
                SatResult::Sat(_)
            ),
            "{backend:?} should accept expected={expected}"
        );

        let mut clauses = base.clauses.clone();
        for &(gate, value) in inputs {
            clauses.push(vec![force(gate, value)]);
        }
        clauses.push(vec![force(output, !expected)]);
        assert!(
            matches!(
                solve_cnf(backend, base.num_vars, clauses, &[], None),
                SatResult::Unsat
            ),
            "{backend:?} should reject expected={}",
            !expected
        );
    }
}

#[test]
fn tseitin_matches_truth_table_for_composed_gates() {
    let mut gates = GateArena::new();
    let a = gates.input();
    let b = gates.input();
    let c = gates.input();
    let xor = gates.xor(a, b);
    let or = gates.or(a, c);
    let output = gates.and(xor, or);

    for av in [false, true] {
        for bv in [false, true] {
            for cv in [false, true] {
                let expected = (av ^ bv) & (av | cv);
                assert_cnf_agrees(&gates, &[(a, av), (b, bv), (c, cv)], output, expected);
            }
        }
    }
}

#[test]
fn tseitin_matches_truth_table_for_mux_and_negation() {
    let mut gates = GateArena::new();
    let s = gates.input();
    let t = gates.input();
    let f = gates.input();
    let mux = gates.mux(s, t, f);
    let output = gates.not(mux);

    for sv in [false, true] {
        for tv in [false, true] {
            for fv in [false, true] {
                let expected = !(if sv { tv } else { fv });
                assert_cnf_agrees(&gates, &[(s, sv), (t, tv), (f, fv)], output, expected);
            }
        }
    }
}
