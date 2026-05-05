use std::io::Read;

fn main() {
    if let Err(err) = run() {
        eprintln!("qfbvsmtrs: {err}");
        std::process::exit(1);
    }
}

fn run() -> qfbvsmtrs::Result<()> {
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
    let query = qfbvsmtrs::parse_smt2(&script)?;
    let result = qfbvsmtrs::Solver::default().solve(&query)?;
    print!("{}", qfbvsmtrs::format_smt2_response(&query, &result));
    Ok(())
}
