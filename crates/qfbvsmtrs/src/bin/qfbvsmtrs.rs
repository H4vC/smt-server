use std::ffi::OsString;
use std::io::Read;
use std::path::PathBuf;

fn main() {
    let worker = std::thread::Builder::new()
        .name("qfbvsmtrs-main".to_owned())
        .stack_size(qfbvsmtrs::DEFAULT_WORKER_STACK_BYTES)
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

#[derive(Debug, Default)]
struct CliOptions {
    input: Option<PathBuf>,
    budget_ms: Option<u64>,
    sat_backend: Option<qfbvsmtrs::SatBackendKind>,
    shortcut_mode: Option<qfbvsmtrs::ShortcutMode>,
    max_input_bytes: Option<u64>,
    trace: bool,
}

fn run() -> qfbvsmtrs::Result<()> {
    let start = std::time::Instant::now();
    let options = parse_args()?;
    let script = read_input(options.input.as_ref(), options.max_input_bytes)?;
    if options.trace {
        eprintln!(
            "qfbvsmtrs trace: read input in {:.3}s",
            start.elapsed().as_secs_f64()
        );
    }
    let parse_start = std::time::Instant::now();
    let query = qfbvsmtrs::parse_smt2(&script)?;
    if options.trace {
        eprintln!(
            "qfbvsmtrs trace: parsed input in {:.3}s (total {:.3}s)",
            parse_start.elapsed().as_secs_f64(),
            start.elapsed().as_secs_f64()
        );
    }
    let mut config = qfbvsmtrs::Config::default();
    if let Some(ms) = options.budget_ms {
        config = config.with_budget(Some(std::time::Duration::from_millis(ms)));
    }
    if let Some(kind) = options.sat_backend {
        config = config.with_sat_backend(kind);
    }
    if let Some(mode) = options.shortcut_mode {
        config = config.with_shortcut_mode(mode);
    }
    let solve_start = std::time::Instant::now();
    let result = qfbvsmtrs::Solver::new(config).solve(&query)?;
    if options.trace {
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

fn parse_args() -> qfbvsmtrs::Result<CliOptions> {
    let mut options = CliOptions {
        trace: std::env::var_os("QFBVSMTRS_TRACE").is_some(),
        ..CliOptions::default()
    };
    if let Some(ms) = std::env::var_os("QFBVSMTRS_BUDGET_MS") {
        options.budget_ms = Some(parse_u64_os("QFBVSMTRS_BUDGET_MS", ms)?);
    }
    if let Some(backend) = std::env::var_os("QFBVSMTRS_SAT_BACKEND") {
        options.sat_backend = Some(parse_sat_backend("QFBVSMTRS_SAT_BACKEND", backend)?);
    }
    if let Some(mode) = std::env::var_os("QFBVSMTRS_SHORTCUT_MODE") {
        options.shortcut_mode = Some(parse_shortcut_mode("QFBVSMTRS_SHORTCUT_MODE", mode)?);
    }
    if let Some(max) = std::env::var_os("QFBVSMTRS_MAX_INPUT_BYTES") {
        options.max_input_bytes = Some(parse_u64_os("QFBVSMTRS_MAX_INPUT_BYTES", max)?);
    }

    let mut input_seen = false;
    let mut args = std::env::args_os().skip(1).peekable();
    while let Some(arg) = args.next() {
        if arg == "--help" || arg == "-h" {
            print_help();
            std::process::exit(0);
        } else if arg == "--trace" {
            options.trace = true;
        } else if arg == "--budget-ms" {
            let value = args
                .next()
                .ok_or_else(|| qfbvsmtrs::Error::invalid("--budget-ms", "missing value"))?;
            options.budget_ms = Some(parse_u64_os("--budget-ms", value)?);
        } else if let Some(value) = split_arg_value(&arg, "--budget-ms=")? {
            options.budget_ms = Some(parse_u64_str("--budget-ms", value)?);
        } else if arg == "--sat-backend" {
            let value = args
                .next()
                .ok_or_else(|| qfbvsmtrs::Error::invalid("--sat-backend", "missing value"))?;
            options.sat_backend = Some(parse_sat_backend("--sat-backend", value)?);
        } else if let Some(value) = split_arg_value(&arg, "--sat-backend=")? {
            options.sat_backend = Some(parse_sat_backend_str("--sat-backend", value)?);
        } else if arg == "--shortcut-mode" {
            let value = args
                .next()
                .ok_or_else(|| qfbvsmtrs::Error::invalid("--shortcut-mode", "missing value"))?;
            options.shortcut_mode = Some(parse_shortcut_mode("--shortcut-mode", value)?);
        } else if let Some(value) = split_arg_value(&arg, "--shortcut-mode=")? {
            options.shortcut_mode = Some(parse_shortcut_mode_str("--shortcut-mode", value)?);
        } else if arg == "--max-input-bytes" {
            let value = args
                .next()
                .ok_or_else(|| qfbvsmtrs::Error::invalid("--max-input-bytes", "missing value"))?;
            options.max_input_bytes = Some(parse_u64_os("--max-input-bytes", value)?);
        } else if let Some(value) = split_arg_value(&arg, "--max-input-bytes=")? {
            options.max_input_bytes = Some(parse_u64_str("--max-input-bytes", value)?);
        } else if arg == "-" {
            if input_seen {
                return Err(qfbvsmtrs::Error::invalid(
                    "command line",
                    "multiple input paths",
                ));
            }
            input_seen = true;
        } else if is_flag_like(&arg) {
            return Err(qfbvsmtrs::Error::invalid(
                "command line",
                format!("unknown option {}", arg.to_string_lossy()),
            ));
        } else {
            if input_seen {
                return Err(qfbvsmtrs::Error::invalid(
                    "command line",
                    "multiple input paths",
                ));
            }
            input_seen = true;
            options.input = Some(PathBuf::from(arg));
        }
    }
    Ok(options)
}

fn split_arg_value<'a>(arg: &'a OsString, prefix: &str) -> qfbvsmtrs::Result<Option<&'a str>> {
    let Some(text) = arg.to_str() else {
        return Ok(None);
    };
    Ok(text.strip_prefix(prefix))
}

fn is_flag_like(arg: &OsString) -> bool {
    arg.to_str()
        .is_some_and(|text| text.starts_with('-') && text != "-")
}

fn parse_u64_os(context: &'static str, value: OsString) -> qfbvsmtrs::Result<u64> {
    let value = value
        .to_str()
        .ok_or_else(|| qfbvsmtrs::Error::invalid(context, "value is not UTF-8"))?;
    parse_u64_str(context, value)
}

fn parse_u64_str(context: &'static str, value: &str) -> qfbvsmtrs::Result<u64> {
    value
        .parse::<u64>()
        .map_err(|_| qfbvsmtrs::Error::invalid(context, "invalid integer"))
}

fn parse_sat_backend(
    context: &'static str,
    value: OsString,
) -> qfbvsmtrs::Result<qfbvsmtrs::SatBackendKind> {
    let value = value
        .to_str()
        .ok_or_else(|| qfbvsmtrs::Error::invalid(context, "value is not UTF-8"))?;
    parse_sat_backend_str(context, value)
}

fn parse_sat_backend_str(
    context: &'static str,
    value: &str,
) -> qfbvsmtrs::Result<qfbvsmtrs::SatBackendKind> {
    match value {
        "splr" => Ok(qfbvsmtrs::SatBackendKind::Splr),
        "varisat" => Ok(qfbvsmtrs::SatBackendKind::Varisat),
        "dpll" => Ok(qfbvsmtrs::SatBackendKind::Dpll),
        _ => Err(qfbvsmtrs::Error::invalid(
            context,
            "expected splr, varisat, or dpll",
        )),
    }
}

fn parse_shortcut_mode(
    context: &'static str,
    value: OsString,
) -> qfbvsmtrs::Result<qfbvsmtrs::ShortcutMode> {
    let value = value
        .to_str()
        .ok_or_else(|| qfbvsmtrs::Error::invalid(context, "value is not UTF-8"))?;
    parse_shortcut_mode_str(context, value)
}

fn parse_shortcut_mode_str(
    context: &'static str,
    value: &str,
) -> qfbvsmtrs::Result<qfbvsmtrs::ShortcutMode> {
    match value {
        "enabled" => Ok(qfbvsmtrs::ShortcutMode::Enabled),
        "disabled" => Ok(qfbvsmtrs::ShortcutMode::Disabled),
        "validate-sat-witnesses" | "validate" => Ok(qfbvsmtrs::ShortcutMode::ValidateSatWitnesses),
        "audit" => Ok(qfbvsmtrs::ShortcutMode::Audit),
        _ => Err(qfbvsmtrs::Error::invalid(
            context,
            "expected enabled, disabled, validate-sat-witnesses, or audit",
        )),
    }
}

fn read_input(path: Option<&PathBuf>, max_input_bytes: Option<u64>) -> qfbvsmtrs::Result<String> {
    let mut script = String::new();
    let limit = max_input_bytes
        .map(|max| {
            max.checked_add(1)
                .ok_or_else(|| qfbvsmtrs::Error::invalid("--max-input-bytes", "value is too large"))
        })
        .transpose()?;
    match path {
        Some(path) => {
            let file = std::fs::File::open(path)
                .map_err(|err| qfbvsmtrs::Error::invalid("input", err.to_string()))?;
            if let Some(limit) = limit {
                file.take(limit)
                    .read_to_string(&mut script)
                    .map_err(|err| qfbvsmtrs::Error::invalid("input", err.to_string()))?;
            } else {
                std::io::BufReader::new(file)
                    .read_to_string(&mut script)
                    .map_err(|err| qfbvsmtrs::Error::invalid("input", err.to_string()))?;
            }
        }
        None => {
            let stdin = std::io::stdin();
            if let Some(limit) = limit {
                stdin
                    .lock()
                    .take(limit)
                    .read_to_string(&mut script)
                    .map_err(|err| qfbvsmtrs::Error::invalid("stdin", err.to_string()))?;
            } else {
                stdin
                    .lock()
                    .read_to_string(&mut script)
                    .map_err(|err| qfbvsmtrs::Error::invalid("stdin", err.to_string()))?;
            }
        }
    }
    if let Some(max) = max_input_bytes {
        let len = u64::try_from(script.len())
            .map_err(|_| qfbvsmtrs::Error::invalid("input", "input length overflow"))?;
        if len > max {
            return Err(qfbvsmtrs::Error::invalid(
                "input",
                format!("input exceeds --max-input-bytes={max}"),
            ));
        }
    }
    Ok(script)
}

fn print_help() {
    println!(
        "qfbvsmtrs [OPTIONS] [FILE]\n\n\
         If FILE is omitted or '-' is used, SMT-LIB is read from stdin.\n\n\
         Options:\n\
           --budget-ms N          Total solver budget in milliseconds\n\
           --sat-backend KIND     SAT backend: splr, varisat, or dpll\n\
           --shortcut-mode MODE   Shortcuts: enabled, disabled, validate-sat-witnesses, or audit\n\
           --max-input-bytes N    Bound SMT-LIB input allocation\n\
           --trace                Print timing trace to stderr\n\
           -h, --help             Show this help\n\n\
         Environment fallbacks: QFBVSMTRS_BUDGET_MS, QFBVSMTRS_SAT_BACKEND,\n\
         QFBVSMTRS_SHORTCUT_MODE, QFBVSMTRS_MAX_INPUT_BYTES, QFBVSMTRS_TRACE."
    );
}
