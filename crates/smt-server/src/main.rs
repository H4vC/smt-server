use std::sync::Arc;

use smt_server::{serve_tcp, ExhaustiveBackend, ServerConfig};

fn main() -> std::io::Result<()> {
    let addr = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:9123".to_owned());
    let backend = Arc::new(ExhaustiveBackend::default());
    eprintln!("smt-server listening on {addr} with exhaustive backend");
    serve_tcp(addr, ServerConfig::new(backend))
}
