# qfbvsmtrs progress report

Date: 2026-05-06

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

Recent full workspace gates after the latest solver/server changes passed:

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
python clients/tests/test_python_client.py
python clients/tests/test_live_server.py
```

Extended randomized validation also passed in this snapshot:

```sh
QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000 cargo test -p qfbvsmtrs --test random_circuits
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
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
- `qfbvsmtrs_corpus_rerun_direct_eq_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sage2_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_asp_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_sydr_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_uclid_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_bouvier_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_float_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_mcm_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_oisc_10s_current_ok.jsonl`
- `qfbvsmtrs_corpus_rerun_smalltail_10s_current_ok.jsonl`

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 42,554 |
| Returned `unknown` against known sat/unsat status | 3,622 |
| Hit hard process timeout | 15 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

This is an improvement of 8,964 additional conclusive corpus answers over the strict baseline, while preserving zero wrong/error results in the merged reports.
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
- additional builder simplifications for extension/constant comparisons, disjoint-bit addition, and 1-bit ITE equality;
- larger dedicated qfbvsmtrs worker stacks in the CLI and smt-server adapter so very deep generated SMT-LIB formulas return `unknown`/timeout instead of aborting with stack overflow.

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
| remaining strict timeout sweep at `--timeout 120` plus bounded BMC follow-up | 16 / 31 timeout-family cases solved; 15 process timeouts remain |
| `spear` SPLR timeout-cushion/current CVS/10s/30s sampled batches | 1,282 additional sampled cases solved before the later current-solver sweep |
| `uclid` SPLR timeout-cushion reruns | 181 additional cases solved before the later current-solver sweep |
| budgeted current-solver rerun over smallest unresolved tail (`qfbvsmtrs_corpus_rerun_direct_eq_ok.jsonl`) | 861 additional cases solved, mostly `Sage2` SAT cases |
| 10s current-solver `Sage2` sweep/continuation (`qfbvsmtrs_corpus_rerun_sage2_10s_current_ok.jsonl`) | 1,139 additional `Sage2` cases solved |
| 30s current-solver `Sage2` sweep (`qfbvsmtrs_corpus_rerun_sage2_30s_current_ok.jsonl`) | 34 additional `Sage2` cases solved |
| bounded `varisat` `Sage2` sweeps (`qfbvsmtrs_corpus_rerun_sage2_varisat_60s_ok.jsonl`) | 132 additional `Sage2` cases solved |
| 10s current-solver `asp` sweep/continuation (`qfbvsmtrs_corpus_rerun_asp_10s_current_ok.jsonl`) | 58 additional `asp` cases solved |
| 30s current-solver `asp` sweep/continuation (`qfbvsmtrs_corpus_rerun_asp_30s_current_ok.jsonl`) | 29 additional `asp` cases solved |
| bounded `varisat` `asp` sweep/continuation (`qfbvsmtrs_corpus_rerun_asp_varisat_60s_ok.jsonl`) | 12 additional `asp` cases solved |
| 10s current-solver `20210219-Sydr` sweep/continuation (`qfbvsmtrs_corpus_rerun_sydr_10s_current_ok.jsonl`) | 189 additional Sydr cases solved |
| 30s current-solver `20210219-Sydr` sweep/continuation (`qfbvsmtrs_corpus_rerun_sydr_30s_current_ok.jsonl`) | 44 additional Sydr cases solved |
| 10s current-solver `uclid` sweep (`qfbvsmtrs_corpus_rerun_uclid_10s_current_ok.jsonl`) | 93 additional `uclid` cases solved |
| 30s current-solver `uclid` sweep/continuation (`qfbvsmtrs_corpus_rerun_uclid_30s_current_ok.jsonl`) | 131 additional `uclid` cases solved |
| 10s current-solver `20210312-Bouvier` sweep (`qfbvsmtrs_corpus_rerun_bouvier_10s_current_ok.jsonl`) | 5 additional Bouvier cases solved |
| 30s current-solver `20210312-Bouvier` sweep (`qfbvsmtrs_corpus_rerun_bouvier_30s_current_ok.jsonl`) | 6 additional Bouvier cases solved |
| bounded `varisat` `20210312-Bouvier` sweeps (`qfbvsmtrs_corpus_rerun_bouvier_varisat_60s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_bouvier_varisat_120s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_bouvier_varisat_240s_ok.jsonl`) | 163 additional Bouvier cases solved |
| 10s current-solver `float` sweep/continuation (`qfbvsmtrs_corpus_rerun_float_10s_current_ok.jsonl`) | 43 additional `float` cases solved |
| 30s current-solver `float` sweep/continuation (`qfbvsmtrs_corpus_rerun_float_30s_current_ok.jsonl`) | 29 additional `float` cases solved |
| 60s current-solver `float` sweep/continuation (`qfbvsmtrs_corpus_rerun_float_60s_current_ok.jsonl`) | 20 additional `float` cases solved |
| bounded `varisat` `float` sweeps (`qfbvsmtrs_corpus_rerun_float_varisat_60s_ok.jsonl`) | 20 additional `float` cases solved |
| 10s current-solver `mcm` sweep (`qfbvsmtrs_corpus_rerun_mcm_10s_current_ok.jsonl`) | 9 additional `mcm` cases solved |
| 30s current-solver `mcm` sweep (`qfbvsmtrs_corpus_rerun_mcm_30s_current_ok.jsonl`) | 4 additional `mcm` cases solved |
| 60s current-solver `mcm` sweep (`qfbvsmtrs_corpus_rerun_mcm_60s_current_ok.jsonl`) | 3 additional `mcm` cases solved |
| bounded `varisat` `mcm` sweeps (`qfbvsmtrs_corpus_rerun_mcm_varisat_60s_ok.jsonl`) | 12 additional `mcm` cases solved |
| bounded `varisat` `brummayerbiere`/`brummayerbiere2` sweeps (`qfbvsmtrs_corpus_rerun_brummayer12_varisat_60s_ok.jsonl`) | 18 additional Brummayer arithmetic cases solved |
| 30s current-solver and no-budget SPLR `brummayerbiere3` sweeps (`qfbvsmtrs_corpus_rerun_brummayerbiere3_30s_current_ok.jsonl`, `qfbvsmtrs_corpus_rerun_brummayerbiere3_splr_nobudget_120s_ok.jsonl`) | 7 additional `brummayerbiere3` cases solved |
| 10s current-solver `20230221-oisc-gurtner` sweep (`qfbvsmtrs_corpus_rerun_oisc_10s_current_ok.jsonl`) | 5 additional OISC cases solved |
| bounded `varisat` `20230221-oisc-gurtner` sweep (`qfbvsmtrs_corpus_rerun_oisc_varisat_60s_ok.jsonl`) | 1 additional OISC case solved |
| 30s current-solver `spear` sweep/continuation (`qfbvsmtrs_corpus_rerun_spear_30s_current_ok.jsonl`) | 319 additional `spear` cases solved |
| 60s current-solver `spear` sweep/continuation (`qfbvsmtrs_corpus_rerun_spear_60s_current_ok.jsonl`) | 64 additional `spear` cases solved |
| 120s current-solver `spear` sweep (`qfbvsmtrs_corpus_rerun_spear_120s_current_ok.jsonl`) | 3 additional `spear` cases solved |
| bounded `varisat` `spear` sweeps (`qfbvsmtrs_corpus_rerun_spear_varisat_60s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_spear_varisat_120s_ok.jsonl`) | 15 additional `spear` cases solved |
| 10s current-solver small-tail sweep (`qfbvsmtrs_corpus_rerun_smalltail_10s_current_ok.jsonl`) | 25 additional smaller-family cases solved |
| bounded `varisat` `uclid` sweep (`qfbvsmtrs_corpus_rerun_uclid_varisat_60s_ok.jsonl`) | 6 additional `uclid_contrib` cases solved |
| bounded `varisat` BMC/Mann sweep (`qfbvsmtrs_corpus_rerun_bmc_mann_varisat_120s_ok.jsonl`) | 16 additional BMC/Mann cases solved |
| bounded `varisat`/no-budget SPLR small-family sweeps (`qfbvsmtrs_corpus_rerun_p4dfa_varisat_60s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_small_varisat_60s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_small_splr_nobudget_60s_ok.jsonl`, `qfbvsmtrs_corpus_rerun_grs_wienand_varisat_60s_ok.jsonl`) | 36 additional smaller-family cases solved |
| `bruttomesso` extensional + LFSR + simple-processor cases | unresolved reduced from 672 to 0 cases |

## Remaining non-conclusive category breakdown

Latest merged unresolved counts under strict/targeted budgets total `3,637` cases: `3,622` `unknown` and `15` process timeouts. The tail is solver-hard and preprocessing-limited rather than parser/front-end failures.

| Category / family | Remaining | Kind split | Expected status split | Character |
|---|---:|---:|---:|---|
| `Sage2` | 2,566 | 2,565 unknown / 1 timeout | 1,381 sat / 1,185 unsat | Dominant tail; large generated BV/SAT instances, mostly hard after bit-blasting. |
| `asp` | 366 | 366 unknown | 286 sat / 80 unsat | Combinatorial puzzle encodings such as N-Queens, TSP, Sokoban, graph coloring, and routing. |
| `20230221-oisc-gurtner` | 106 | 106 unknown | 12 sat / 94 unsat | OISC/program-transition style nested BV constraints. |
| `mcm` | 103 | 103 unknown | 76 sat / 27 unsat | Arithmetic/synthesis-style BV constraints. |
| `brummayerbiere*` arithmetic/bit-hack families | 91 | 91 unknown | 5 sat / 86 unsat | Bit-hack, overflow, min/max, multiplication, and integer-root identities. |
| `20210219-Sydr` | 91 | 91 unknown | 91 sat / 0 unsat | Symbolic-execution/path-constraint formulas, including symbolic-memory cases. |
| `float` | 79 | 79 unknown | 41 sat / 38 unsat | Floating-point-style arithmetic encoded as pure bit-vectors. |
| `log-slicing` | 57 | 57 unknown | 0 sat / 57 unsat | All remaining cases are division/remainder/multiplication equivalences: `bvmul`, `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`. |
| `20210312-Bouvier` | 26 | 26 unknown | 25 sat / 1 unsat | Remaining generated `vlsat3_*` cases after bounded `varisat` reruns. |
| `bmc-bv` + `bmc-bv-svcomp14` | 18 | 5 unknown / 13 timeout | 6 sat / 12 unsat | BMC transition-system cases; includes most process timeouts. |
| `spear` | 6 | 6 unknown | 6 sat / 0 unsat | Symbolic-execution C program VCs; small OpenLDAP tail remains after 30s/60s/120s sweeps. |
| `uclid` + `uclid_contrib_smtcomp09` | 3 | 3 unknown | 2 sat / 1 unsat | Program/circuit verification constraints. |
| Other smaller families | 125 | 124 unknown / 1 timeout | 58 sat / 67 unsat | Smaller tails across `20221214-p4dfa-XiaoqiChen`, `20230224-grsbits-truby`, `2019-Wolf-fmbench`, `calypto`, `RWS`, `fft`, `wienand-cav2008`, `VS3`, and other single-digit families. |

The `15` process timeouts are concentrated in `bmc-bv-svcomp14` (`11`), `bmc-bv` (`2`), `Sage2/bench_9140.smt2` (`1`), and `2019-Mann/ridecore-qf_bv-bug.smt2` (`1`).

## Production-readiness assessment

`qfbvsmtrs` is ready for continued integration testing and controlled experimentation as a third backend in `smt-server`. It is not yet ready to claim production completeness for arbitrary SMT-LIB QF_BV because:

- latest merged corpus still has `3,622` `unknown` cases and `15` timeouts under strict budgets/targeted reruns;
- full no-budget/no-timeout corpus completion has not been demonstrated;
- full-corpus Z3 differential testing has not been completed;
- a long-running fuzzing campaign has not been completed;
- some important families (`Sage2`, `asp`, `mcm`, `20230221-oisc-gurtner`, `float`, and `20210219-Sydr`) still need major performance/simplification work.

## Recommended next steps

1. Run a full workspace gate after the latest solver changes.
2. Continue merged incremental corpus reruns, always skipping known-good `ok` cases.
3. Prioritize `Sage2`, then `asp`/remaining `spear`, which dominate the remaining non-conclusive set.
4. Add stronger word-level preprocessing for symbolic execution path constraints, byte extraction/concatenation, and equality propagation.
5. Extend log-slicing recognition to the remaining multiplication/division/remainder encodings where safe.
6. Run broader Z3 differential tests over the corpus using the Rust `z3` crate.
7. Run an actual fuzzing campaign, not just a compile check.
8. Reassess production readiness only after the remaining corpus tail is either solved or bounded by documented, accepted limits.
