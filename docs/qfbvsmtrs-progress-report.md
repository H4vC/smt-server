# qfbvsmtrs progress report

Date: 2026-05-05

`qfbvsmtrs` is now implemented as a standalone pure-Rust QF_BV solver crate and is integrated into `smt-server` as a third backend. The solver is functional, broadly tested, and has produced no wrong conclusive answers on the SMT-LIB 2025 QF_BV corpus runs performed so far. It is **not yet production-complete for arbitrary QF_BV workloads** because a large tail of corpus cases still returns `unknown` or hits timeout under strict budgets.

## Current status

| Area | Status |
|---|---|
| Standalone crate | Implemented in `crates/qfbvsmtrs` |
| Native Rust builder API | Implemented via `qfbvsmtrs::Builder` |
| SMT-LIB frontend | Implemented via `parse_smt2`, `solve_smt2`, and response formatting |
| SAT backends | `splr` default, `varisat` selectable, internal DPLL fallback/testing |
| Bit-blasting pipeline | Implemented for broad QF_BV Bool/BV operator coverage |
| Model extraction | Implemented for SAT results when requested |
| Named unsat cores | Implemented by deletion-based minimization |
| Optimization | Implemented for `minimize`/`maximize` by bit-hunt |
| Server integration | Implemented as `QfbvsmtrsBackend`, raced with Z3 and binbit |
| Corpus runner | Implemented as resumable append-only JSONL runner |
| Fuzz target | Added and compile-checked |

## Validation performed

Checked-in validation includes:

- exhaustive 4-bit arithmetic/comparison/shift/division circuit tests;
- randomized 16/32/64-bit circuit property tests;
- Tseitin truth-table tests across SAT backends;
- known-answer SMT-LIB fixtures;
- Rust `z3` differential smoke tests;
- all-backend SAT/UNSAT tests for `splr`, `varisat`, and DPLL;
- standalone solver tests for SAT, UNSAT, model extraction, push/pop, cores, optimization, and division-by-zero semantics;
- `smt-server` integration tests for qfbvsmtrs SAT, UNSAT, model, core, and optimization paths;
- fuzz harness compile check.

Recent full workspace gates after the latest solver and documentation changes passed:

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
```

These gates should still be rerun before any release or production-ready claim, especially after further corpus-driven solver changes.

## SMT-LIB QF_BV corpus status

Corpus: SMT-LIB 2025 non-incremental QF_BV archive from Zenodo record `16740866`.

Local corpus:

- `46,191` `.smt2` files;
- about `37.3 GB` decompressed;
- reports stored under `target/smtlib/` and not checked into the repository.

### Full strict-budget baseline

Report: `target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl`

Budget: `QFBVSMTRS_BUDGET_MS=3000`, process timeout `30s`.

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 33,590 |
| Returned `unknown` against known sat/unsat status | 10,771 |
| Hit hard process timeout | 1,830 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

### Latest merged incremental status

Merged reports:

- `qfbvsmtrs_corpus_report_v3.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_extract.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app1.jsonl`
- `qfbvsmtrs_corpus_rerun_pspace_patterns.jsonl`
- `qfbvsmtrs_corpus_rerun_challenge_overflow.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_extcmp_sample.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_addsub.jsonl`
- `qfbvsmtrs_corpus_rerun_brummayerbiere4_consteval.jsonl`
- `qfbvsmtrs_corpus_rerun_challenge_signed_overflow.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_polynomial.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_extensional.jsonl`

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 34,327 |
| Returned `unknown` against known sat/unsat status | 10,048 |
| Hit hard process timeout | 1,816 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

This is an improvement of 737 additional conclusive corpus answers over the strict baseline, while preserving zero wrong/error results in the merged reports.

## Recent solver improvements

Recent targeted improvements include:

- solver preprocessing shortcuts for wide `pspace` arithmetic-order patterns;
- SAT witness shortcut by evaluating all-zero/all-one assignments for satisfiable formulas when no model/core is requested;
- arithmetic pattern detection for unsigned and signed multiplication-overflow guard proofs;
- log-slicing adder/subtractor equivalence recognition;
- extensional extract/concat candidate contradiction detection for Bruttomesso `ext_con` cases;
- limited polynomial equality normalization for 32/64-bit rewrite verification cases;
- additional builder simplifications for extension/constant comparisons and 1-bit ITE equality.

Targeted corpus effects observed:

| Family/pass | Result |
|---|---:|
| `pspace` successor/power-of-two/shift-add patterns | 86 / 86 rerun cases solved |
| `brummayerbiere4` constant-assignment SAT witnesses | 10 / 10 rerun cases solved |
| `challenge` unsigned/signed overflow guards | 2 / 2 cases solved after combined passes |
| `log-slicing` add/sub patterns | 42 / 208 rerun cases solved |
| `20190311-bv-term-small-rw-Noetzli` polynomial/linear rewrites | unresolved reduced to 37 cases |
| `bruttomesso` extensional cases | unresolved reduced from 672 to 258 cases |

## Largest remaining non-conclusive groups

Latest merged unresolved counts under strict budgets:

| Family | Non-conclusive |
|---|---:|
| `Sage2` | 5,005 |
| `sage` | 2,488 |
| `spear` | 1,689 |
| `asp` | 465 |
| `uclid` | 407 |
| `20210219-Sydr` | 344 |
| `bruttomesso` | 258 |
| `20210312-Bouvier` | 200 |
| `float` | 191 |
| `log-slicing` | 166 |
| `mcm` | 131 |
| `20230221-oisc-gurtner` | 112 |

## Production-readiness assessment

`qfbvsmtrs` is ready for continued integration testing and controlled experimentation as a third backend in `smt-server`. It is not yet ready to claim production completeness for arbitrary SMT-LIB QF_BV because:

- latest merged corpus still has `10,048` `unknown` cases and `1,816` timeouts under strict budgets;
- full no-budget/no-timeout corpus completion has not been demonstrated;
- full-corpus Z3 differential testing has not been completed;
- a long-running fuzzing campaign has not been completed;
- some important families (`Sage2`, `sage`, `spear`, `asp`, `uclid`) still need major performance/simplification work.

## Recommended next steps

1. Run a full workspace gate after the latest solver changes.
2. Continue merged incremental corpus reruns, always skipping known-good `ok` cases.
3. Prioritize `Sage2`, `sage`, and `spear`, which dominate the remaining non-conclusive set.
4. Add stronger word-level preprocessing for symbolic execution path constraints, byte extraction/concatenation, and equality propagation.
5. Extend log-slicing recognition beyond add/sub to shifts, comparisons, multiplication, and division where safe.
6. Run broader Z3 differential tests over the corpus using the Rust `z3` crate.
7. Run an actual fuzzing campaign, not just a compile check.
8. Reassess production readiness only after the remaining corpus tail is either solved or bounded by documented, accepted limits.
