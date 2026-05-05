use std::path::Path;

use qfbvsmtrs::{solve_smt2, Config, SolveStatus};

#[test]
fn differential_random_formulas_against_z3_smoke() {
    let mut rng = Rng::new(0x5a33_d1ff_5154_4c49);
    for index in 0..20 {
        let script = random_script(&mut rng, 2, 4, 8);
        compare_with_z3(&script, &format!("generated-smoke-{index}"));
    }
}

#[test]
fn differential_random_formulas_against_z3_production_when_enabled() {
    if std::env::var("QFBVSMTRS_DIFF_RANDOM").ok().as_deref() != Some("1") {
        eprintln!("skipping extended random differential test; set QFBVSMTRS_DIFF_RANDOM=1");
        return;
    }
    let mut rng = Rng::new(0x5154_4c49_5a33_d1ff);
    for index in 0..200 {
        let script = random_script(&mut rng, 4, 4, 8);
        compare_with_z3(&script, &format!("generated-production-{index}"));
    }
}

#[test]
fn differential_smtlib_corpus_against_z3_when_configured() {
    let Some(root) = std::env::var_os("QFBVSMTRS_SMTLIB_DIR") else {
        eprintln!("skipping SMT-LIB corpus differential test; set QFBVSMTRS_SMTLIB_DIR");
        return;
    };

    let limit = std::env::var("QFBVSMTRS_SMTLIB_LIMIT")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(500);
    let mut files = Vec::new();
    collect_smt2(Path::new(&root), &mut files);
    files.sort();
    for path in files.into_iter().take(limit) {
        let script = std::fs::read_to_string(&path).expect("read .smt2");
        compare_with_z3(&script, &path.display().to_string());
    }
}

fn compare_with_z3(script: &str, label: &str) {
    let ours = solve_smt2(script, &Config::default())
        .unwrap_or_else(|err| panic!("{label}: qfbvsmtrs error: {err}"));
    let z3 = run_z3_crate(script);
    assert_eq!(ours.status, z3, "{label}\n{script}");
}

fn run_z3_crate(script: &str) -> SolveStatus {
    let solver = z3::Solver::new();
    solver.from_string(script);
    match solver.check() {
        z3::SatResult::Sat => SolveStatus::Sat,
        z3::SatResult::Unsat => SolveStatus::Unsat,
        z3::SatResult::Unknown => SolveStatus::Unknown,
    }
}

fn collect_smt2(path: &Path, out: &mut Vec<std::path::PathBuf>) {
    if path.is_file() {
        if path.extension().is_some_and(|ext| ext == "smt2") {
            out.push(path.to_owned());
        }
        return;
    }
    let Ok(entries) = std::fs::read_dir(path) else {
        return;
    };
    for entry in entries.flatten() {
        collect_smt2(&entry.path(), out);
    }
}

fn random_script(rng: &mut Rng, depth: usize, vars: usize, width: u32) -> String {
    let lhs = random_bv_expr(rng, depth, vars, width);
    let rhs = random_bv_expr(rng, depth, vars, width);
    let predicate = match rng.next() % 8 {
        0 => format!("(= {lhs} {rhs})"),
        1 => format!("(bvult {lhs} {rhs})"),
        2 => format!("(bvule {lhs} {rhs})"),
        3 => format!("(bvslt {lhs} {rhs})"),
        4 => format!("(bvsle {lhs} {rhs})"),
        5 => format!("(not (= {lhs} {rhs}))"),
        6 => format!("(= (bvadd {lhs} #x00) {lhs})"),
        _ => format!("(= (bvsub (bvadd {lhs} {rhs}) {rhs}) {lhs})"),
    };
    let decls = (0..vars)
        .map(|i| format!("(declare-const x{i} (_ BitVec {width}))\n"))
        .collect::<String>();
    format!("(set-logic QF_BV)\n{decls}(assert {predicate})\n(check-sat)\n")
}

fn random_bv_expr(rng: &mut Rng, depth: usize, vars: usize, width: u32) -> String {
    if depth == 0 {
        if rng.next().is_multiple_of(2) {
            format!("x{}", rng.next() as usize % vars)
        } else {
            let hex_digits = (width as usize).div_ceil(4);
            let mask = if width == 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            format!("#x{:0hex_digits$x}", rng.next() & mask)
        }
    } else {
        let a = random_bv_expr(rng, depth - 1, vars, width);
        let b = random_bv_expr(rng, depth - 1, vars, width);
        match rng.next() % 13 {
            0 => format!("(bvnot {a})"),
            1 => format!("(bvneg {a})"),
            2 => format!("(bvand {a} {b})"),
            3 => format!("(bvor {a} {b})"),
            4 => format!("(bvxor {a} {b})"),
            5 => format!("(bvadd {a} {b})"),
            6 => format!("(bvsub {a} {b})"),
            7 => format!("(bvmul {a} {b})"),
            8 => format!("(bvshl {a} {b})"),
            9 => format!("(bvlshr {a} {b})"),
            10 => format!("(bvashr {a} {b})"),
            11 => format!("(bvudiv {a} {b})"),
            _ => format!("(bvurem {a} {b})"),
        }
    }
}

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}
