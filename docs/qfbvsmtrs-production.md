# qfbvsmtrs production validation

`qfbvsmtrs` is a standalone pure-Rust QF_BV solver crate integrated into `smt-server` as `QfbvsmtrsBackend`.

## SAT backends

- Default: `splr` CDCL SAT solver with timeout support. The adapter gives SPLR a small internal CPU-time cushion because SPLR can report timeout conservatively under Windows/parallel corpus load; outer caller deadlines/process timeouts remain the production guardrail.
- Alternate: `varisat` CDCL SAT solver for cross-checking and experiments.
- Fallback/testing: internal DPLL solver.

Select a backend with `Config::with_sat_backend(SatBackendKind::...)`.

## Production-complete bar

For this solver, a practical production-complete claim means the supported QF_BV subset is sound, bounded, and regression-tested under documented limits:

- no known wrong `sat`/`unsat` answers;
- requested models validate, and unsupported/expensive artifacts fail cleanly or return `unknown`;
- solver budgets, process timeouts, and memory-heavy failure modes are documented and respected;
- unsupported SMT-LIB constructs are rejected instead of mis-solved;
- remaining corpus `unknown`/timeout cases are either solved or explicitly accepted as outside the production guarantee;
- `smt-server` integration handles `sat`, `unsat`, `unknown`, timeout, model, core, and optimization paths correctly while `qfbvsmtrs` remains standalone.

Current status: sound controlled backend, not production-complete for arbitrary QF_BV corpus workloads because the merged SMT-LIB corpus tail is still `7,175` `unknown` plus `16` timeouts.

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

The corpus runs found no wrong conclusive answers. Latest merged targeted status is 39,000 conclusive matches, 7,175 `unknown`, and 16 timeouts. The remaining tail is primarily hard SAT/preprocessing work: `Sage2`, `asp`, `spear`, `20210219-Sydr`, `uclid`, generated arithmetic/float-style cases, and BMC transition-system timeouts.
