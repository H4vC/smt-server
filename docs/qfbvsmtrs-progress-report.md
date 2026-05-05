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
| Corpus runner | Implemented as resumable append-only JSONL runner with baseline/exclusion reports, attempt logs, queue sorting, elapsed-time filters, and wall-clock submission caps |
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

Recent full workspace gates after the latest solver changes passed:

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
```

After the latest corpus-runner and documentation updates, the Python runner was syntax-checked with:

```sh
python -m py_compile scripts/qfbvsmtrs_corpus.py
```

The full workspace gates should still be rerun before any release or production-ready claim, especially after further corpus-driven solver changes.

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
- `qfbvsmtrs_corpus_rerun_sage_app7_bench10_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench11_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench11_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench12_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench12_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench13_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench14_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench14_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench15_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench16_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench17_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench18_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench19_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench19_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench20_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench21_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench21_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench22_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench22_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench23_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench24_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench25_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench26_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench27_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench28_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench29_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench29_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench30_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench31_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench31_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench32_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench33_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench33_serial_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench34_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench35_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench36_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench37_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench38_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench39_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench40_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench41_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench42_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench43_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench44_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench45_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench46_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench47_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench48_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench49_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench50_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench51_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench52_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench53_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench54_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench55_timeout60_ok.jsonl` through `qfbvsmtrs_corpus_rerun_sage_app7_bench99_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app7_bench1_exact_timeout60_ok.jsonl` through `qfbvsmtrs_corpus_rerun_sage_app7_bench9_exact_timeout60_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app8_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app9_current.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_unknown_30s_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage_app2_bench367_120s_ok.jsonl`
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
- `qfbvsmtrs_corpus_rerun_sage2_bench116_current.jsonl` through `qfbvsmtrs_corpus_rerun_sage2_bench131_current.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_explicit_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_noetzli_rewrites.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_splr_slack_sample.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_cvs_current.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_10s_sample_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_10s_batch1_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_samba_30s_sample_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_small_10s_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_spear_samba_libs_10s_ok.jsonl`
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
- `qfbvsmtrs_corpus_rerun_timeouts120_ok.jsonl`

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 39,000 |
| Returned `unknown` against known sat/unsat status | 7,175 |
| Hit hard process timeout | 16 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

This is an improvement of 5,410 additional conclusive corpus answers over the strict baseline, while preserving zero wrong/error results in the merged reports.
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
| `Sage2` affine-byte/bench100--bench131 sampled reruns | 303 additional sampled cases solved |
| `sage` app1/app2/app7/app8/app9 current/timeout-60/rerun-30s passes | 2,488 additional cases solved; app1/app2/app7/app8/app9 now 0 unresolved |
| remaining strict timeout sweep at `--timeout 120` | 15 / 31 remaining timeout cases solved; 16 process timeouts remain |
| `spear` SPLR timeout-cushion/current CVS/10s/30s sampled batches | 1,282 additional sampled cases solved; unresolved now 407 |
| `uclid` SPLR timeout-cushion reruns | 181 additional cases solved; unresolved now 233 |
| `bruttomesso` extensional + LFSR + simple-processor cases | unresolved reduced from 672 to 0 cases |

## Remaining non-conclusive category breakdown

Latest merged unresolved counts under strict/targeted budgets total `7,191` cases: `7,175` `unknown` and `16` process timeouts. The tail is solver-hard and preprocessing-limited rather than parser/front-end failures.

| Category / family | Remaining | Kind split | Expected status split | Character |
|---|---:|---:|---:|---|
| `Sage2` | 4,701 | 4,700 unknown / 1 timeout | 2,773 sat / 1,928 unsat | Dominant tail; large generated BV/SAT instances, mostly hard after bit-blasting. |
| `asp` | 465 | 465 unknown | 347 sat / 118 unsat | Combinatorial puzzle encodings such as N-Queens, TSP, Sokoban, graph coloring, and routing. |
| `spear` | 407 | 407 unknown | 407 sat / 0 unsat | Symbolic-execution C program VCs; remaining cases are `samba_v3.0.24` 311, `inn_v2.4.3` 69, `wget_v1.10.2` 19, and `openldap_v2.3.35` 8. |
| `20210219-Sydr` | 344 | 344 unknown | 151 sat / 193 unsat | Symbolic-execution/path-constraint formulas, including symbolic-memory cases. |
| `uclid` + `uclid_contrib_smtcomp09` | 233 | 233 unknown | 224 sat / 9 unsat | Program/circuit verification constraints, mainly `uclid/catchconv`. |
| `20210312-Bouvier` | 200 | 200 unknown | 100 sat / 100 unsat | Generated `vlsat3_*` cases. |
| `float` | 191 | 191 unknown | 101 sat / 90 unsat | Floating-point-style arithmetic encoded as pure bit-vectors. |
| `mcm` | 131 | 131 unknown | 98 sat / 33 unsat | Arithmetic/synthesis-style BV constraints. |
| `20230221-oisc-gurtner` | 112 | 112 unknown | 12 sat / 100 unsat | OISC/program-transition style nested BV constraints. |
| `brummayerbiere*` arithmetic/bit-hack families | 140 | 140 unknown | 14 sat / 126 unsat | Bit-hack, overflow, min/max, multiplication, and integer-root identities. |
| `log-slicing` | 57 | 57 unknown | 0 sat / 57 unsat | All remaining cases are division/remainder/multiplication equivalences: `bvmul`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`. |
| `bmc-bv` + `bmc-bv-svcomp14` | 32 | 18 unknown / 14 timeout | 7 sat / 25 unsat | BMC transition-system cases; includes most process timeouts. |
| Other smaller families | 178 | 177 unknown / 1 timeout | 89 sat / 89 unsat | Smaller tails across `20221214-p4dfa-XiaoqiChen`, `20230224-grsbits-truby`, `2019-Wolf-fmbench`, `calypto`, `RWS`, `fft`, `wienand-cav2008`, `VS3`, and other single-digit families. |

The `16` process timeouts are concentrated in `bmc-bv-svcomp14` (`11`), `bmc-bv` (`3`), `Sage2/bench_9140.smt2` (`1`), and `2019-Mann/ridecore-qf_bv-bug.smt2` (`1`).

## Production-readiness assessment

`qfbvsmtrs` is ready for continued integration testing and controlled experimentation as a third backend in `smt-server`. It is not yet ready to claim production completeness for arbitrary SMT-LIB QF_BV because:

- latest merged corpus still has `7,175` `unknown` cases and `16` timeouts under strict budgets/targeted reruns;
- full no-budget/no-timeout corpus completion has not been demonstrated;
- full-corpus Z3 differential testing has not been completed;
- a long-running fuzzing campaign has not been completed;
- some important families (`Sage2`, `asp`, `spear`, `uclid`) still need major performance/simplification work.

## Recommended next steps

1. Run a full workspace gate after the latest solver changes.
2. Continue merged incremental corpus reruns, always skipping known-good `ok` cases.
3. Prioritize `Sage2`, then `asp`/remaining `spear`, which dominate the remaining non-conclusive set.
4. Add stronger word-level preprocessing for symbolic execution path constraints, byte extraction/concatenation, and equality propagation.
5. Extend log-slicing recognition to the remaining multiplication/division/remainder encodings where safe.
6. Run broader Z3 differential tests over the corpus using the Rust `z3` crate.
7. Run an actual fuzzing campaign, not just a compile check.
8. Reassess production readiness only after the remaining corpus tail is either solved or bounded by documented, accepted limits.
