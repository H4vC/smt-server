# Backend provisioning

The reference server now builds with two solver backends:

- `Z3Backend` uses the Rust `z3` crate and links Z3 through the crate's `gh-release` feature, so it does not shell out to a `z3` executable.
- `BinbitBackend` uses the Rust `binbit` solver from `https://github.com/bint-disasm/binbit`.

The default server (`crates/smt-server/src/main.rs`) races both backends via `RacingBackend`.

No standalone `z3` binary is required at runtime, and the old exhaustive/test backend and Z3 CLI adapter have been removed from the public server configuration.
