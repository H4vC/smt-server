use std::fs;
use std::time::Instant;

use qfbvsmtrs::{solve_smt2, Config};

const BUILT_INS: &[(&str, &str)] = &[
    (
        "8bit-add-model",
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= (bvadd x #x01) #x2b))\n(check-sat)\n(get-model)\n",
    ),
    (
        "16bit-mul-unsat",
        "(set-logic QF_BV)\n(assert (not (= (bvmul #x00ff #x0101) #xffff)))\n(check-sat)\n",
    ),
    (
        "8bit-div-zero",
        "(set-logic QF_BV)\n(assert (= (bvudiv #x07 #x00) #xff))\n(assert (= (bvurem #x07 #x00) #x07))\n(check-sat)\n",
    ),
];

fn main() -> std::process::ExitCode {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut cases = Vec::new();
    if args.is_empty() {
        cases.extend(
            BUILT_INS
                .iter()
                .map(|(name, script)| ((*name).to_owned(), (*script).to_owned())),
        );
    } else {
        for path in args {
            match fs::read_to_string(&path) {
                Ok(script) => cases.push((path, script)),
                Err(err) => {
                    eprintln!("failed to read {path}: {err}");
                    return std::process::ExitCode::FAILURE;
                }
            }
        }
    }

    println!("case,status,elapsed_ms");
    for (name, script) in cases {
        let start = Instant::now();
        match solve_smt2(&script, &Config::default()) {
            Ok(result) => println!(
                "{},{:?},{:.3}",
                name,
                result.status,
                start.elapsed().as_secs_f64() * 1000.0
            ),
            Err(err) => {
                println!(
                    "{},error,{:.3}",
                    name,
                    start.elapsed().as_secs_f64() * 1000.0
                );
                eprintln!("{name}: {err}");
                return std::process::ExitCode::FAILURE;
            }
        }
    }
    std::process::ExitCode::SUCCESS
}
