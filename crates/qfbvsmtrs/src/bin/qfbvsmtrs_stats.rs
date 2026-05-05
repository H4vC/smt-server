use std::time::Instant;

fn main() {
    let worker = std::thread::Builder::new()
        .name("qfbvsmtrs-stats".to_owned())
        .stack_size(64 * 1024 * 1024)
        .spawn(run)
        .expect("spawn qfbvsmtrs stats worker");
    match worker.join() {
        Ok(Ok(())) => {}
        Ok(Err(err)) => {
            eprintln!("qfbvsmtrs_stats: {err}");
            std::process::exit(1);
        }
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

fn run() -> qfbvsmtrs::Result<()> {
    let path = std::env::args_os()
        .nth(1)
        .ok_or_else(|| qfbvsmtrs::Error::invalid("usage", "qfbvsmtrs_stats <file.smt2>"))?;
    let start = Instant::now();
    let script = std::fs::read_to_string(path)
        .map_err(|err| qfbvsmtrs::Error::invalid("input", err.to_string()))?;
    let read = start.elapsed();
    let parse_start = Instant::now();
    let query = qfbvsmtrs::parse_smt2(&script)?;
    let parse = parse_start.elapsed();
    let blast_start = Instant::now();
    let blasted = qfbvsmtrs::blast::blast_query(&query)?;
    let blast = blast_start.elapsed();
    let cnf_start = Instant::now();
    let cnf = qfbvsmtrs::cnf::encode(&blasted.gates, blasted.assertion);
    let cnf_time = cnf_start.elapsed();
    println!(
        "read_s,{:.3},parse_s,{:.3},blast_s,{:.3},cnf_s,{:.3},terms,{},gates,{},vars,{},clauses,{}",
        read.as_secs_f64(),
        parse.as_secs_f64(),
        blast.as_secs_f64(),
        cnf_time.as_secs_f64(),
        query.arena.len(),
        blasted.gates.gates().len(),
        cnf.num_vars,
        cnf.clauses.len()
    );
    Ok(())
}
