use std::sync::Arc;

use smt_server::{serve_tcp, ExhaustiveBackend, RacingBackend, ServerConfig, Z3CliBackend};

fn main() -> std::io::Result<()> {
    let addr = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:9123".to_owned());
    let backend = Arc::new(RacingBackend::new(vec![
        Arc::new(ExhaustiveBackend::default()),
        Arc::new(Z3CliBackend::default()),
    ]));
    eprintln!("smt-server listening on {addr} with racing backend (exhaustive + z3-cli)");
    serve_tcp(addr, ServerConfig::new(backend))
}
