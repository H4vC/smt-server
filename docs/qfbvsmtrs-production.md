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

Current status: sound controlled backend, not production-complete for arbitrary QF_BV corpus workloads because the merged SMT-LIB corpus tail is still `3,266` `unknown` plus `15` timeouts.

## `smt-server` production hardening status

Recent integration hardening added bounded TCP frame/response sizes, bounded active connections, bounded cache entries/key sizes/response sizes, client-side response-size limits, stricter response/request validation, unknown-reason propagation, racing budget bounds (including a 30s default budget in the shipped racing server binary for requests that omit one), pinned the git `binbit` dependency by revision, validates SAT backend assignments against the emitted CNF before returning `sat`, and enforces that conclusive backend answers include requested model/core/optimization artifacts on binary, text, and standalone SMT-LIB formatting paths. Budgeted `smt-server` calls to `QfbvsmtrsBackend` use qfbvsmtrs' polling DPLL SAT backend to avoid in-process SPLR timeout overruns; unbudgeted standalone/default qfbvsmtrs still uses SPLR. The server text path now falls back to qfbvsmtrs' standalone SMT-LIB parser/solver for `qfbvsmtrs` and shipped `racing` backends when the legacy wire-building frontend rejects a QF_BV script, with a bounded 30s default budget overrideable via `SMT_SERVER_TEXT_QFBVSMTRS_BUDGET_MS`. The standalone CLI now exposes explicit `--budget-ms`, `--sat-backend`, and `--max-input-bytes` controls (with matching environment fallbacks) so production callers can bound solve time and input allocation. The SMT-LIB compatibility frontends now accept common QF_BV forms such as `set-info`, decimal indexed literals `(_ bvN W)`, `distinct`, n-ary `=`, and non-recursive `define-fun` macros, while malformed indexed operators/annotations are rejected without panics.

Remaining service-level production work includes stronger backend cancellation for racing loser threads and continued corpus triage for the qfbvsmtrs text fallback/parser path on very large SMT-LIB inputs.

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

The checked-in default suite includes exhaustive 4-bit circuit tests, randomized 16/32/64-bit circuit properties, Tseitin truth-table tests across all SAT backends, known-answer SMT-LIB fixtures, Z3 differential smoke tests through the Rust `z3` crate, standalone solver tests, total-deadline regression tests for optimization, and server integration tests. In the latest snapshot, the 10k random-circuit extended gate and `QFBVSMTRS_DIFF_RANDOM=1` random Z3 differential gate also passed; a long `cargo fuzz` campaign is still outstanding because `cargo-fuzz` is not installed in the current environment.

See also:

- `docs/qfbvsmtrs-progress-report.md` for the current implementation/corpus status.
- `docs/qfbvsmtrs-design-report.md` for the solver architecture and design details.
- `docs/qfbvsmtrs-corpus-results.md` for SMT-LIB QF_BV corpus command history.

The corpus runs found no wrong conclusive answers. Latest merged targeted status is 42,910 conclusive matches, 3,266 `unknown`, and 15 timeouts after the `bvurem` fixed-point, Favaro MBA, Yurichev popcount, polynomial definition-chain/pack-equivalence reasoning, Brummayer popcount bit-hack recognition, Brummayer leading-zero simplification hardening, budgeted current-solver tail rerun, 10s/30s/60s/120s/240s sweeps for `Sage2`, `spear`, `asp`, `20210219-Sydr`, `uclid`, `float`, `mcm`, `20221214-p4dfa-XiaoqiChen`, and `brummayerbiere3`, bounded `varisat` sweeps for `Sage2`, `20210312-Bouvier`, `asp`, `spear`, `float`, `mcm`, `20230221-oisc-gurtner`, `uclid`, `20221214-p4dfa-XiaoqiChen`, BMC/Mann, Brummayer arithmetic families, Brummayer leading-zero cases, `log-slicing`, and small families, plus a 60s SPLR `log-slicing` multiplication follow-up and a small-tail 10s sweep. The remaining tail is primarily hard SAT/preprocessing work: `Sage2`, `asp`, `mcm`, `20230221-oisc-gurtner`, generated arithmetic/float-style cases, and BMC transition-system timeouts.
