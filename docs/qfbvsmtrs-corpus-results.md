# qfbvsmtrs SMT-LIB QF_BV corpus run

Corpus used: SMT-LIB release 2025, non-incremental `QF_BV.tar.zst` from Zenodo record `16740866`.

Local corpus size:

- compressed: `1,732,883,333` bytes
- decompressed SMT-LIB: `46,191` `.smt2` files, about `37.3 GB`

## Current strict-budget run

Report: `target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl`

Command shape:

```sh
cargo build --release -p qfbvsmtrs
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --exe target/release/qfbvsmtrs.exe \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 12 \
  --report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl
```

Result:

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 33,590 |
| Returned `unknown` against a known sat/unsat status | 10,771 |
| Hit the hard process timeout | 1,830 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

The current full run has no parser/frontend errors and no wrong conclusive answers, but it is still not production-complete for arbitrary SMT-LIB QF_BV workloads because 12,601 files remain non-conclusive under this strict budget.

Targeted incremental reruns after adding associative/commutative BV add/mul canonicalization, scaled-add folding, simple shifted-product rewrites, extract/concat simplifications, and a few broad arithmetic pattern shortcuts improved several slices:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains 20190311-bv-term-small-rw-Noetzli \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8
```

Additional targeted runs used the same baseline/merge mechanism for `bruttomesso`, `sage/app1`, `pspace`, and `challenge`:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains bruttomesso \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_bruttomesso_extract.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8

python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_bruttomesso_extract.jsonl \
  --rerun-kinds unknown,timeout \
  --path-regex "sage.*app1" \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_sage_app1.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8

python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_bruttomesso_extract.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_sage_app1.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains pspace \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_pspace_patterns.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8

python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli_linear.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_bruttomesso_extract.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_sage_app1.jsonl \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_rerun_pspace_patterns.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains challenge \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_challenge_overflow.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 4
```

Merged with the full baseline these targeted passes yield:

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 33,835 |
| Returned `unknown` against a known sat/unsat status | 10,531 |
| Hit the hard process timeout | 1,825 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

## Latest merged status

Additional incremental reports after the earlier passes include targeted reruns for `Sage2` samples, `sage` app slices, `log-slicing` add/sub/comparison/shift cases, `brummayerbiere4`, `challenge`, Noetzli polynomial/algebraic rewrite cases, Bruttomesso extensional/LFSR/simple-processor cases, sampled/high-budget `spear` batches, `uclid`, and the final timeout sweep.

Latest merged-by-path status across the full baseline and targeted reports currently stands at:

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 39,000 |
| Returned `unknown` against a known sat/unsat status | 7,175 |
| Hit the hard process timeout | 16 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

Remaining non-conclusive cases by category:

| Category / family | Remaining | Kind split | Expected status split | Character |
|---|---:|---:|---:|---|
| `Sage2` | 4,701 | 4,700 unknown / 1 timeout | 2,773 sat / 1,928 unsat | Large generated BV/SAT instances; dominant hard tail. |
| `asp` | 465 | 465 unknown | 347 sat / 118 unsat | Combinatorial puzzle encodings: N-Queens, TSP, Sokoban, graph coloring, routing, etc. |
| `spear` | 407 | 407 unknown | 407 sat / 0 unsat | Symbolic-execution C VCs; remaining mainly `samba`, `inn`, `wget`, and `openldap`. |
| `20210219-Sydr` | 344 | 344 unknown | 151 sat / 193 unsat | Symbolic-execution/path-constraint formulas, including symbolic memory. |
| `uclid` + `uclid_contrib_smtcomp09` | 233 | 233 unknown | 224 sat / 9 unsat | Program/circuit verification constraints. |
| `20210312-Bouvier` | 200 | 200 unknown | 100 sat / 100 unsat | Generated `vlsat3_*` cases. |
| `float` | 191 | 191 unknown | 101 sat / 90 unsat | Floating-point-style arithmetic encoded as pure BV. |
| `mcm` | 131 | 131 unknown | 98 sat / 33 unsat | Arithmetic/synthesis-style BV constraints. |
| `20230221-oisc-gurtner` | 112 | 112 unknown | 12 sat / 100 unsat | OISC/program-transition style nested BV constraints. |
| `brummayerbiere*` arithmetic/bit-hack families | 140 | 140 unknown | 14 sat / 126 unsat | Bit-hack, overflow, min/max, multiplication, and integer-root identities. |
| `log-slicing` | 57 | 57 unknown | 0 sat / 57 unsat | Remaining division/remainder/multiplication equivalences. |
| `bmc-bv` + `bmc-bv-svcomp14` | 32 | 18 unknown / 14 timeout | 7 sat / 25 unsat | BMC transition-system cases; includes most process timeouts. |
| Other smaller families | 178 | 177 unknown / 1 timeout | 89 sat / 89 unsat | Smaller tails across p4dfa, grsbits, fmbench, calypto, RWS, fft, VS3, and other families. |

The `16` process timeouts are concentrated in `bmc-bv-svcomp14` (`11`), `bmc-bv` (`3`), `Sage2/bench_9140.smt2` (`1`), and `2019-Mann/ridecore-qf_bv-bug.smt2` (`1`).

See `docs/qfbvsmtrs-progress-report.md` for the current progress summary and `docs/qfbvsmtrs-design-report.md` for solver architecture.

## Incremental reruns

The corpus runner is append-only and resumable. It can now use a prior report as a baseline and skip known-good files:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --rerun-kinds unknown,timeout \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_30s.jsonl \
  --budget-ms 30000 \
  --timeout 120 \
  --workers 8
```

Restrict a rerun to one benchmark family:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains 20190311-bv-term-small-rw-Noetzli \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_noetzli.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8
```

Selection dry-run:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --rerun-kinds unknown,timeout \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_30s.jsonl \
  --list-only
```

For the original strict full-run baseline this queues 12,601 non-conclusive files and skips 33,590 known-good files. With the latest merged targeted reports, the non-conclusive set is down to 7,191 files. Re-running the same command resumes automatically because paths already present in the output report are skipped. Multiple `--baseline-report` arguments can be supplied; later reports override earlier records by path, so follow-up runs can skip cases solved by prior incremental passes.

Improvement-only experimental runs can avoid recording unknown/timeout regressions while still preserving solved cases:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report_v3.jsonl \
  --rerun-kinds unknown,timeout \
  --path-contains Sage2 \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_sage2_next_ok.jsonl \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 8 \
  --record-ok-only
```

For slower exploratory batches, keep the official report improvement-only but also write a separate attempt log. The attempt log records every result kind and can be excluded from later exploratory runs without folding unknown/timeout regressions into the official merged status:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_merged_current_official.jsonl \
  --exclude-report target/smtlib/qfbvsmtrs_corpus_attempt_spear_30s.jsonl \
  --rerun-kinds unknown \
  --path-contains spear \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_spear_30s_ok.jsonl \
  --attempt-report target/smtlib/qfbvsmtrs_corpus_attempt_spear_30s.jsonl \
  --record-ok-only \
  --budget-ms 30000 \
  --timeout 90 \
  --workers 4 \
  --max-wall-seconds 900
```

Use `--min-baseline-elapsed` / `--max-baseline-elapsed` and `--sort-by baseline-elapsed-asc` to split a family into fast/slow bins. Path filters match both the report's native path spelling and a normalized forward-slash spelling, so `--path-regex 'spear/(inn_v2\.4\.3|wget_v1\.10\.2)/'` works on Windows reports. `--timeout` is a per-file process timeout; total wall time is roughly `queued * min(budget, timeout) / workers` for batches that mostly return `unknown`, so use `--limit`, lower `--workers`, and `--max-wall-seconds` to keep exploratory runs bounded.
