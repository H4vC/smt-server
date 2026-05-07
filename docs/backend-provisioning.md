# Backend provisioning

The reference server now builds with one simplifier backend and three solver backends:

- `Z3Backend` uses the Rust `z3` crate and links Z3 through the crate's `gh-release` feature, so it does not shell out to a `z3` executable.
- `BinbitBackend` uses the Rust `binbit` solver from `https://github.com/bint-disasm/binbit`.
- `QfbvsmtrsBackend` uses the standalone pure-Rust `qfbvsmtrs` crate in this workspace. It translates validated `smt-wire` requests into the crate's own IR, bit-blasts to CNF, solves with the crate's selectable pure-Rust SAT backend (`splr` by default, with `varisat` and internal DPLL available for cross-checking), and supports models, named unsat cores, and bit-hunt optimization.
- `RumbaBackend` uses `rumba-core` from `https://github.com/thalium/rumba` for `SIMPLIFY` requests over 64-bit-or-smaller MBA expression islands (`~`, unary `-`, `&`, `|`, `^`, `+`, `-`, `*`). Unsupported requests return the original target expression.

The default server (`crates/smt-server/src/main.rs`) routes `SIMPLIFY` to `RumbaBackend` via `CommandRouterBackend` and races all three solver backends via `RacingBackend` for solve/optimization requests.

No standalone `z3` binary is required at runtime, and the old exhaustive/test backend and Z3 CLI adapter have been removed from the public server configuration.
