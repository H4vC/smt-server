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

Additional incremental reports after the earlier passes include targeted reruns for `Sage2` samples, `sage` app slices, `log-slicing` add/sub/comparison/shift cases, `brummayerbiere4`, `challenge`, Noetzli polynomial/algebraic rewrite cases, Bruttomesso extensional/LFSR/simple-processor cases, sampled `spear`, and `uclid`.

Latest merged-by-path status across the full baseline and targeted reports currently stands at:

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 35,519 |
| Returned `unknown` against a known sat/unsat status | 8,953 |
| Hit the hard process timeout | 1,719 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

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

For the original strict full-run baseline this queues 12,601 non-conclusive files and skips 33,590 known-good files. With the latest merged targeted reports, the non-conclusive set is down to 10,672 files. Re-running the same command resumes automatically because paths already present in the output report are skipped. Multiple `--baseline-report` arguments can be supplied; later reports override earlier records by path, so follow-up runs can skip cases solved by prior incremental passes.

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
