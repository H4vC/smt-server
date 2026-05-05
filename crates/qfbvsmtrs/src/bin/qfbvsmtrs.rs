use std::io::Read;

fn main() {
    let worker = std::thread::Builder::new()
        .name("qfbvsmtrs-main".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("spawn qfbvsmtrs worker");
    match worker.join() {
        Ok(Ok(())) => {}
        Ok(Err(err)) => {
            eprintln!("qfbvsmtrs: {err}");
            std::process::exit(1);
        }
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn run() -> qfbvsmtrs::Result<()> {
    let trace = std::env::var_os("QFBVSMTRS_TRACE").is_some();
    let start = std::time::Instant::now();
    let mut args = std::env::args_os();
    let _program = args.next();
    let script = if let Some(path) = args.next() {
        std::fs::read_to_string(path)
            .map_err(|err| qfbvsmtrs::Error::invalid("input", err.to_string()))?
    } else {
        let mut script = String::new();
        std::io::stdin()
            .read_to_string(&mut script)
            .map_err(|err| qfbvsmtrs::Error::invalid("stdin", err.to_string()))?;
        script
    };
    if trace {
        eprintln!(
            "qfbvsmtrs trace: read input in {:.3}s",
            start.elapsed().as_secs_f64()
        );
    }
    let parse_start = std::time::Instant::now();
    let query = qfbvsmtrs::parse_smt2(&script)?;
    if trace {
        eprintln!(
            "qfbvsmtrs trace: parsed input in {:.3}s (total {:.3}s)",
            parse_start.elapsed().as_secs_f64(),
            start.elapsed().as_secs_f64()
        );
    }
    let mut config = qfbvsmtrs::Config::default();
    if let Ok(ms) = std::env::var("QFBVSMTRS_BUDGET_MS") {
        let ms = ms
            .parse::<u64>()
            .map_err(|_| qfbvsmtrs::Error::invalid("QFBVSMTRS_BUDGET_MS", "invalid integer"))?;
        config = config.with_budget(Some(std::time::Duration::from_millis(ms)));
    }
    if let Ok(backend) = std::env::var("QFBVSMTRS_SAT_BACKEND") {
        let kind = match backend.as_str() {
            "splr" => qfbvsmtrs::SatBackendKind::Splr,
            "varisat" => qfbvsmtrs::SatBackendKind::Varisat,
            "dpll" => qfbvsmtrs::SatBackendKind::Dpll,
            _ => {
                return Err(qfbvsmtrs::Error::invalid(
                    "QFBVSMTRS_SAT_BACKEND",
                    "expected splr, varisat, or dpll",
                ))
            }
        };
        config = config.with_sat_backend(kind);
    }
    let solve_start = std::time::Instant::now();
    let result = qfbvsmtrs::Solver::new(config).solve(&query)?;
    if trace {
        eprintln!(
            "qfbvsmtrs trace: solved in {:.3}s (total {:.3}s)",
            solve_start.elapsed().as_secs_f64(),
            start.elapsed().as_secs_f64()
        );
        if result.status == qfbvsmtrs::SolveStatus::Unknown {
            if let Some(message) = &result.message {
                eprintln!("qfbvsmtrs trace: unknown: {message}");
            }
        }
    }
    print!("{}", qfbvsmtrs::format_smt2_response(&query, &result));
    Ok(())
}
