# qfbvsmtrs validation and corpus status

`qfbvsmtrs` is a sound, bounded pure-Rust QF_BV backend under the tested contract, but it is not claimed to solve every arbitrary QF_BV benchmark within small budgets. The production posture is: return correct conclusive answers when possible, validate requested artifacts, and return `unknown` rather than guessing when limits are hit.

## Production-complete bar

A production-complete claim for this crate would require:

- no known wrong `sat`/`unsat` answers;
- returned models validate against formulas and requested model variables;
- unsupported or expensive artifacts fail cleanly or return `unknown`;
- budgets, process timeouts, and memory-heavy failure modes are documented and respected;
- unsupported SMT-LIB constructs are rejected rather than mis-solved;
- remaining corpus `unknown`/timeout cases are either solved or explicitly accepted as outside the guarantee;
- `smt-server` integration correctly handles `sat`, `unsat`, `unknown`, model, core, simplification, optimization, cache, and text/binary formatting paths while qfbvsmtrs remains standalone.

Current status: no wrong conclusive answers in the recorded corpus runs, but the merged SMT-LIB QF_BV tail still contains `3,266` `unknown` results and `15` process timeouts.

## Required local gates

Run these before pushing normal changes:

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
python3 python/tests/test_python_client.py
python3 python/tests/test_live_server.py
cmake -S cpp -B /tmp/smt_cpp_cmake
cmake --build /tmp/smt_cpp_cmake
cargo build -p smt-server
target/debug/smt-server 127.0.0.1:9123 &
server_pid=$!
trap 'kill "$server_pid" 2>/dev/null || true' EXIT
sleep 1
SMT_SERVER_ADDRESS=127.0.0.1:9123 ctest --test-dir /tmp/smt_cpp_cmake --output-on-failure
```

The checked-in suite includes exhaustive 4-bit circuit tests, randomized circuit properties, Tseitin truth-table tests across SAT backends, known-answer SMT-LIB fixtures, Rust Z3 differential smoke tests, standalone qfbvsmtrs tests, server binary/text/cache/racing tests, live client tests, and C++/Python smoke tests.

## Extended gates

Use these for solver changes, release candidates, and corpus-driven work:

```sh
QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000 cargo test -p qfbvsmtrs --test random_circuits
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
QFBVSMTRS_SMTLIB_DIR=/path/to/SMT-LIB/QF_BV cargo test -p qfbvsmtrs --test differential_z3
cargo fuzz run smt2_pipeline --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
cargo run -p qfbvsmtrs --bin qfbvsmtrs_bench -- path/to/query.smt2
```

## SMT-LIB corpus snapshot

Corpus: SMT-LIB release 2025, non-incremental `QF_BV.tar.zst` from Zenodo record `16740866`.

Local corpus size from the recorded run:

- compressed: `1,732,883,333` bytes;
- decompressed: `46,191` `.smt2` files, about `37.3 GB`.

Latest merged-by-path status across the full strict-budget baseline and targeted incremental reruns:

| Class | Count |
|---|---:|
| Conclusive and matched `:status` | 42,910 |
| Returned `unknown` against a known sat/unsat status | 3,266 |
| Hit the hard process timeout | 15 |
| Frontend/backend error | 0 |
| Conclusive wrong answer | 0 |

Remaining non-conclusive categories:

| Category / family | Remaining | Character |
|---|---:|---|
| `Sage2` | 2,305 | Large generated BV/SAT instances; dominant hard tail. |
| `asp` | 342 | Combinatorial puzzle encodings such as N-Queens, TSP, Sokoban, coloring, routing. |
| `20230221-oisc-gurtner` | 106 | OISC/program-transition style nested BV constraints. |
| `mcm` | 97 | Arithmetic/synthesis-style BV constraints. |
| `20210219-Sydr` | 91 | Symbolic-execution/path-constraint formulas. |
| `float` | 72 | Floating-point-style arithmetic encoded as pure BV. |
| `brummayerbiere*` arithmetic/bit-hack families | 71 | Bit-hack, overflow, min/max, multiplication, integer-root identities. |
| `log-slicing` | 55 | Remaining division/remainder/multiplication equivalences. |
| `20210312-Bouvier` | 23 | Remaining generated `vlsat3_*` cases. |
| `bmc-bv` + `bmc-bv-svcomp14` | 18 | BMC transition-system cases; contains most process timeouts. |
| `spear` | 5 | Symbolic-execution C verification conditions. |
| Other smaller families | 96 | Smaller tails across p4dfa, grsbits, fmbench, calypto, RWS, fft, VS3, and others. |

The 15 process timeouts were concentrated in `bmc-bv-svcomp14` (11), `bmc-bv` (2), `Sage2/bench_9140.smt2` (1), and `2019-Mann/ridecore-qf_bv-bug.smt2` (1).

## Corpus runner usage

Build the CLI first:

```sh
cargo build --release -p qfbvsmtrs
```

Run a strict baseline:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --exe target/release/qfbvsmtrs \
  --budget-ms 3000 \
  --timeout 30 \
  --workers 12 \
  --report target/smtlib/qfbvsmtrs_corpus_report.jsonl
```

Rerun only non-conclusive cases from one or more baselines:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report.jsonl \
  --rerun-kinds unknown,timeout \
  --report target/smtlib/qfbvsmtrs_corpus_rerun.jsonl \
  --budget-ms 30000 \
  --timeout 120 \
  --workers 8
```

Restrict by family or path:

```sh
python scripts/qfbvsmtrs_corpus.py target/smtlib/QF_BV-2025 \
  --baseline-report target/smtlib/qfbvsmtrs_corpus_report.jsonl \
  --rerun-kinds unknown,timeout \
  --path-component asp \
  --report target/smtlib/qfbvsmtrs_corpus_rerun_asp.jsonl \
  --budget-ms 10000 \
  --timeout 60 \
  --workers 4
```

Useful runner features:

- append-only JSONL reports and resumable execution;
- multiple `--baseline-report` arguments, merged latest-by-path;
- `--list-only` for dry-run queue inspection;
- `--record-ok-only` for official improvement-only reports;
- `--attempt-report` plus `--exclude-report` for bounded exploratory batches;
- path filters by substring, regex, or exact path component;
- elapsed-time filters and queue sorting for splitting slow families;
- `--max-wall-seconds` to cap exploratory wall-clock time.

Keep full report files under `target/` or another untracked location. Only summarize durable results in this document.
