# Second backend evaluation

Phase 5 evaluated the planned second-backend options against the current repository constraints: dependency-free CI on Windows, macOS, and Linux, no required system solver in the build, and a backend interface that can race multiple implementations.

## binbit

`binbit` is attractive for bit-blasting workloads, but its public API and cross-platform packaging are not stable enough here to make it a mandatory CI dependency. It remains a candidate backend behind the `Backend` trait once packaging is pinned.

## Bitwuzla

Bitwuzla has strong QF_BV support, but introducing its native library would make CI and local setup substantially heavier. It is also best added after the protocol/server surface is stable.

## Implemented choice

The repository now includes two practical backends:

1. `ExhaustiveBackend`: dependency-free, deterministic, cross-platform, and useful for tests/small queries.
2. `Z3CliBackend`: translates validated wire IR to SMT-LIB and invokes a `z3` executable when one is available.

`RacingBackend` can race these (or future binbit/Bitwuzla adapters) and returns the first conclusive result while preserving `UNKNOWN` fallback behavior.
