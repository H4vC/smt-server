use std::sync::Arc;

use smt_server::{
    serve_tcp, BinbitBackend, CommandRouterBackend, QfbvsmtrsBackend, RacingBackend, RumbaBackend,
    ServerConfig, Z3Backend,
};

fn main() -> std::io::Result<()> {
    let addr = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:9123".to_owned());
    let solver = Arc::new(
        RacingBackend::new(vec![
            Arc::new(Z3Backend),
            Arc::new(BinbitBackend),
            Arc::new(QfbvsmtrsBackend),
        ])
        .with_default_budget_ms(30_000),
    );
    let backend = Arc::new(CommandRouterBackend::new(Arc::new(RumbaBackend), solver));
    eprintln!(
        "smt-server listening on {addr} with rumba simplifier + racing solver (z3 crate + binbit + qfbvsmtrs)"
    );
    serve_tcp(addr, ServerConfig::new(backend))
}
