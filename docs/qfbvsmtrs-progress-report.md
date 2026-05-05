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
- `qfbvsmtrs_corpus_rerun_sage_app1_current2.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app2_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench10_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench11_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench12_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app8_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app9_current.jsonl`
- `qfbvsmtrs_corpus_rerun_pspace_patterns.jsonl`
- `qfbvsmtrs_corpus_rerun_challenge_overflow.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_extcmp_sample.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_addsub.jsonl`
- `qfbvsmtrs_corpus_rerun_brummayerbiere4_consteval.jsonl`
- `qfbvsmtrs_corpus_rerun_challenge_signed_overflow.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_polynomial.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_extensional.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_affine_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench100_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench100_single.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench101_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench102_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench103_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench104_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench105_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench106_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench107_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench108_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench109_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench110_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench111_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench112_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench113_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench114_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_bench115_current.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_explicit_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_rewrites.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_splr_slack_sample.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_cvs_current.jsonl`
- `qfbvsmtrs_corpus_rerun_uclid_slack_sample.jsonl`
- `qfbvsmtrs_corpus_rerun_uclid_slack_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_lfsr.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_simple_processor_single.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_simple_processor_shortcut.jsonl`
- `qfbvsmtrs_corpus_rerun_bruttomesso_simple_processor_shortcut2.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_cmp.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_bvult.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_bvshl.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_bvlshr.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_bvashr.jsonl`
- `qfbvsmtrs_corpus_rerun_logslicing_bvmul_30s.jsonl`

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 35,519 |
| Returned `unknown` against known sat/unsat status | 8,953 |
| Hit hard process timeout | 1,719 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

This is an improvement of 1,929 additional conclusive corpus answers over the strict baseline, while preserving zero wrong/error results in the merged reports.
## Recent solver improvements

Recent targeted improvements include:

- solver preprocessing shortcuts for wide `pspace` arithmetic-order patterns;
- SAT witness shortcut by evaluating all-zero/all-one and small deterministic seeded assignments for satisfiable formulas when no model/core is requested;
- arithmetic pattern detection for unsigned and signed multiplication-overflow guard proofs;
- log-slicing adder/subtractor, signed/unsigned comparison, and shift equivalence recognition;
- extensional extract/concat candidate contradiction detection for Bruttomesso `ext_con` cases;
- limited polynomial equality normalization for 32/64-bit rewrite verification cases;
- sparse constant-multiplication bit-blasting for low-Hamming-weight constants;
- additional Noetzli-style algebraic simplifications for complement/absorption laws, `bvlshr x x`, shift/negation distribution, and shifted-product normalization;
- affine byte SAT witnesses and small explicit assignment witnesses for model-free SAT queries;
- synchronized Bruttomesso LFSR contradiction recognition for reset-controlled duplicate/injective state machines;
- Bruttomesso simple-processor decode/output equivalence contradiction recognition;
- corpus-runner `--record-kinds` / `--record-ok-only` support for improvement-only experimental backend runs;
- additional builder simplifications for extension/constant comparisons, disjoint-bit addition, and 1-bit ITE equality.

Targeted corpus effects observed:

| Family/pass | Result |
|---|---:|
| `pspace` successor/power-of-two/shift-add patterns | 86 / 86 rerun cases solved |
| `brummayerbiere4` constant-assignment SAT witnesses | 10 / 10 rerun cases solved |
| `challenge` unsigned/signed overflow guards | 2 / 2 cases solved after combined passes |
| `log-slicing` add/sub, comparison, shifts, and high-budget small multiplication cases | 151 / 208 rerun cases solved; unresolved now 57 |
| `20190311-bv-term-small-rw-Noetzli` polynomial/linear/Noetzli rewrites | remaining 37 cases solved; unresolved now 0 |
| `Sage2` affine-byte/bench100--bench115 sampled reruns | 120 additional sampled cases solved |
| `sage` app1/app2/app7/app8/app9 current reruns | 477 additional cases solved; app8/app9 now 0 unresolved |
| `spear` SPLR timeout-cushion/current CVS samples | 10 additional sampled cases solved |
| `uclid` SPLR timeout-cushion reruns | 181 additional cases solved; unresolved now 233 |
| `bruttomesso` extensional + LFSR + simple-processor cases | unresolved reduced from 672 to 0 cases |

## Largest remaining non-conclusive groups

Latest merged unresolved counts under strict budgets:

| Family | Non-conclusive |
|---|---:|
| `Sage2` | 4,885 |
| `sage` | 2,011 |
| `spear` | 1,679 |
| `asp` | 466 |
| `uclid` | 233 |
| `20210219-Sydr` | 344 |
| `20210312-Bouvier` | 200 |
| `float` | 194 |
| `log-slicing` | 57 |
| `mcm` | 131 |
| `20230221-oisc-gurtner` | 112 |

## Production-readiness assessment

`qfbvsmtrs` is ready for continued integration testing and controlled experimentation as a third backend in `smt-server`. It is not yet ready to claim production completeness for arbitrary SMT-LIB QF_BV because:

- latest merged corpus still has `8,953` `unknown` cases and `1,719` timeouts under strict budgets/targeted reruns;
- full no-budget/no-timeout corpus completion has not been demonstrated;
- full-corpus Z3 differential testing has not been completed;
- a long-running fuzzing campaign has not been completed;
- some important families (`Sage2`, `sage`, `spear`, `asp`, `uclid`) still need major performance/simplification work.

## Recommended next steps

1. Run a full workspace gate after the latest solver changes.
2. Continue merged incremental corpus reruns, always skipping known-good `ok` cases.
3. Prioritize `Sage2`, `sage`, and `spear`, which dominate the remaining non-conclusive set.
4. Add stronger word-level preprocessing for symbolic execution path constraints, byte extraction/concatenation, and equality propagation.
5. Extend log-slicing recognition to the remaining multiplication/division/remainder encodings where safe.
6. Run broader Z3 differential tests over the corpus using the Rust `z3` crate.
7. Run an actual fuzzing campaign, not just a compile check.
8. Reassess production readiness only after the remaining corpus tail is either solved or bounded by documented, accepted limits.
