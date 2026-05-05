# qfbvsmtrs production validation

`qfbvsmtrs` is a standalone pure-Rust QF_BV solver crate integrated into `smt-server` as `QfbvsmtrsBackend`.

## SAT backends

- Default: `splr` CDCL SAT solver with timeout support. The adapter gives SPLR a small internal CPU-time cushion because SPLR can report timeout conservatively under Windows/parallel corpus load; outer caller deadlines/process timeouts remain the production guardrail.
- Alternate: `varisat` CDCL SAT solver for cross-checking and experiments.
- Fallback/testing: internal DPLL solver.

Select a backend with `Config::with_sat_backend(SatBackendKind::...)`.

## Required local gates

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
```

## Extended validation gates

```sh
QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000 cargo test -p qfbvsmtrs --test random_circuits
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
QFBVSMTRS_SMTLIB_DIR=/path/to/SMT-LIB/QF_BV cargo test -p qfbvsmtrs --test differential_z3
cargo fuzz run smt2_pipeline --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
cargo run -p qfbvsmtrs --bin qfbvsmtrs_bench -- path/to/query.smt2
```

The checked-in default suite includes exhaustive 4-bit circuit tests, randomized 16/32/64-bit circuit properties, Tseitin truth-table tests across all SAT backends, known-answer SMT-LIB fixtures, Z3 differential smoke tests through the Rust `z3` crate, standalone solver tests, and server integration tests.

See also:

- `docs/qfbvsmtrs-progress-report.md` for the current implementation/corpus status.
- `docs/qfbvsmtrs-design-report.md` for the solver architecture and design details.
- `docs/qfbvsmtrs-corpus-results.md` for SMT-LIB QF_BV corpus command history.

The corpus runs found no wrong conclusive answers. Latest merged targeted status is 35,519 conclusive matches, 8,953 `unknown`, and 1,719 timeouts, so the solver is not yet production-complete for arbitrary corpus workloads.
