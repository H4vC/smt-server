# Backend provisioning

The reference server now builds with three solver backends:

- `Z3Backend` uses the Rust `z3` crate and links Z3 through the crate's `gh-release` feature, so it does not shell out to a `z3` executable.
- `BinbitBackend` uses the Rust `binbit` solver from `https://github.com/bint-disasm/binbit`.
- `QfbvsmtrsBackend` uses the standalone pure-Rust `qfbvsmtrs` crate in this workspace. It translates validated `smt-wire` requests into the crate's own IR, bit-blasts to CNF, solves with the crate's selectable pure-Rust SAT backend (`splr` by default, with `varisat` and internal DPLL available for cross-checking), and supports models, named unsat cores, and bit-hunt optimization.

The default server (`crates/smt-server/src/main.rs`) races all three backends via `RacingBackend`.

No standalone `z3` binary is required at runtime, and the old exhaustive/test backend and Z3 CLI adapter have been removed from the public server configuration.
