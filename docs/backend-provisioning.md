# Backend provisioning

The reference server always builds with the packaged `exhaustive` backend. It is deterministic and dependency-free, intended for tests, golden vectors, malformed-input checks, and small QF_BV/Bool queries.

The `z3-cli` backend adapter is available for deployments that install the `z3` executable on `PATH`:

- Windows: install a Z3 release from <https://github.com/Z3Prover/z3/releases> and add the directory containing `z3.exe` to `PATH`.
- macOS: `brew install z3`.
- Linux: use the distribution package (`apt install z3`, `dnf install z3`, etc.) or a release archive from Z3Prover.

CI does not require Z3; it verifies the portable exhaustive backend on Windows, macOS, and Linux. Z3-specific integration can be enabled in deployments by selecting `Z3CliBackend` or using it as one of the racing backends.
