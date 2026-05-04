use std::sync::Arc;

use smt_server::{serve_tcp, BinbitBackend, RacingBackend, ServerConfig, Z3Backend};

fn main() -> std::io::Result<()> {
    let addr = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:9123".to_owned());
    let backend = Arc::new(RacingBackend::new(vec![
        Arc::new(Z3Backend),
        Arc::new(BinbitBackend),
    ]));
    eprintln!("smt-server listening on {addr} with racing backend (z3 crate + binbit)");
    serve_tcp(addr, ServerConfig::new(backend))
}
