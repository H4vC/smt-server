# Solver backend integration

The server currently integrates three real solver backends behind the shared `Backend` trait:

1. `Z3Backend` (`crates/smt-server/src/z3_backend.rs`) translates validated wire IR directly to Rust `z3` crate ASTs, uses `Solver::check_assumptions`, extracts models and named unsat cores, and implements optimization with a server-side bit-hunt over Z3 assumptions.
2. `BinbitBackend` (`crates/smt-server/src/binbit_backend.rs`) translates validated wire IR directly to `binbit::SmtSolver`, including assumptions, named unsat cores, model extraction, and binbit's native min/max helpers.
3. `QfbvsmtrsBackend` (`crates/smt-server/src/qfbvsmtrs_backend.rs`) adapts validated wire IR into the standalone `qfbvsmtrs` crate, which owns its own IR, SMT-LIB frontend, bit-blaster, CNF encoder, selectable pure-Rust SAT backends (`splr`, `varisat`, internal DPLL), model extraction, bit-hunt optimization, and deletion-based named unsat-core extraction.

`RacingBackend` can race Z3, binbit, and qfbvsmtrs and returns the first conclusive result while continuing to log later backend disagreements.

The previous dependency-free `ExhaustiveBackend` and external-process `Z3CliBackend` were removed from the active server API/configuration. The default executable now starts `RacingBackend(Z3Backend, BinbitBackend, QfbvsmtrsBackend)`.
