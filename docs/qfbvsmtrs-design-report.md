# qfbvsmtrs design report

Date: 2026-05-05

`qfbvsmtrs` is a standalone pure-Rust solver for SMT-LIB QF_BV formulas. It is also integrated into this repository's `smt-server` as `QfbvsmtrsBackend`. The core design goal is that the solver crate remains independently usable: server integration is an adapter, not a dependency from the solver back into `smt-server`.

## High-level architecture

```text
Standalone API / SMT-LIB text / smt-wire request
        |
        v
qfbvsmtrs Query IR
        |
        v
Eager word-level simplification + solver preprocessing
        |
        v
Reachability-filtered bit-blasting
        |
        v
Structurally hashed Boolean gate graph
        |
        v
Deadline-aware Tseitin CNF encoding
        |
        v
Pure-Rust SAT backend: splr / varisat / DPLL
        |
        v
SolveResult: sat/model, unsat/core, optimum, unknown
```

The pipeline is intentionally conventional: keep the word-level layer simple and sound, bit-blast to Boolean circuits, encode to CNF, then delegate search to a SAT solver. Most production work now focuses on reducing the amount of bit-blasting/SAT search by adding safe word-level simplifications and family-specific generalizations that recognize common SMT-LIB benchmark patterns.

## Crate layout

Core crate: `crates/qfbvsmtrs`

| File | Responsibility |
|---|---|
| `lib.rs` | Public exports and optional `wire` feature gate |
| `config.rs` | Solver configuration, budget, SAT backend selection |
| `error.rs` | Solver-local `Error` and `Result` types |
| `ir.rs` | Hash-consed term arena, `TermId`, `Sort`, `NodeKind` |
| `query.rs` | Query, assertions, assumptions, commands, optimization target |
| `builder.rs` | Native Rust builder API plus eager simplification hooks |
| `frontend.rs` | SMT-LIB parsing/lowering and SMT-LIB response formatting |
| `wire.rs` | Optional `smt-wire` bridge behind `wire` feature |
| `gates.rs` | Boolean gate arena with structural hashing |
| `circuits.rs` | Bit-vector circuits over Boolean gates |
| `blast.rs` | IR-to-gate bit-blaster with reachable-term filtering |
| `cnf.rs` | Tseitin CNF encoder with clause normalization and deadlines |
| `sat.rs` | SAT backend dispatch: `splr`, `varisat`, DPLL |
| `model.rs` | SAT assignment to qfbvsmtrs model values |
| `solver.rs` | Top-level solve/optimize/core orchestration and preprocessing |
| `eval.rs` | Constant-assignment evaluator used for cheap SAT witness detection |
| `simplify.rs` | Simplification module placeholder/documentation hook |

Server integration lives in `crates/smt-server/src/qfbvsmtrs_backend.rs` and converts between server `QueryResult` values and qfbvsmtrs `SolveResult` values.

## Public entry points

The crate supports three input paths into the same solver core.

### SMT-LIB text

```rust
let result = qfbvsmtrs::solve_smt2(script, &qfbvsmtrs::Config::default())?;
```

This path parses SMT-LIB, builds a `Query`, solves it, and can format the response back to SMT-LIB text.

### Native builder API

```rust
let mut b = qfbvsmtrs::Builder::new();
let x = b.bv_var("x", 8)?;
let one = b.bv_const(1, 8)?;
let target = b.bv_add(x, one)?;
let two = b.bv_const(2, 8)?;
let eq = b.bv_eq(target, two)?;
b.assert(eq)?;
let query = b.finish()?;
let result = qfbvsmtrs::Solver::new(Default::default()).solve(&query)?;
```

The builder performs eager simplification while constructing terms.

### `smt-wire` bridge

With feature `wire`, the crate can lower `smt-wire` expressions/requests into qfbvsmtrs queries. This keeps server integration thin while preserving qfbvsmtrs as a standalone crate.

## IR design

The IR is a sorted, hash-consed DAG:

- `TermId` is a compact index into the arena.
- Every node has a `Sort`: `Bool` or `Bv(width)`.
- `Arena::add` structurally hashes `(NodeKind, Sort)`, so identical subterms share one `TermId`.
- Sort and width checks happen at construction boundaries.
- The arena is append-only, which makes it easy to process terms in topological order.

The IR stores both Boolean and bit-vector terms in one arena. This avoids a separate Boolean AST layer and makes mixed nodes such as `BvIte`, `BoolIte`, comparisons, and overflow predicates straightforward.

## SMT-LIB frontend

The SMT-LIB frontend is based on `yaspar`. It supports the QF_BV subset used by the solver, including:

- declarations and definitions (`declare-fun`, `define-fun`, `define-const`);
- Boolean connectives and n-ary equality/distinct;
- QF_BV arithmetic, bitwise, comparison, extraction, concatenation, extension, repeat, rotate, and overflow-style operators covered by the IR;
- `let` expansion;
- scoped assertions via `push`/`pop`;
- model/value/core-oriented commands that map to qfbvsmtrs query flags.

The parser lowers directly through the builder, so parser-time construction benefits from the same eager simplifications as native API users.

## Word-level simplification

The builder is the main simplification hook. It performs local, sound rewrites before bit-blasting. Current classes include:

- Boolean constants, double negation, idempotence, contradiction/tautology pairs;
- BV constant folding for arithmetic/bitwise/shift/extract/concat/extension/repeat/rotate/comparison operations;
- BV identities and annihilators such as `x + 0`, `x * 1`, `x & 0`, `x | 0`, `x ^ 0`;
- structural `extract(extract(...))`, `extract(concat(...))`, and adjacent-extract concat merging;
- associative/commutative canonicalization for `bvadd` and `bvmul`;
- scaled add-term folding such as `x + x -> 2*x`;
- shifted product/add rewrites;
- extension/constant equality and unsigned comparison reductions;
- 1-bit ITE equality reduction;
- wide possible-bit-mask reasoning for disjoint `bvadd`, `bvand`, and `bvxor` reductions on packed-byte/shifted-slice terms;
- limited polynomial equality normalization for small-to-medium rewrite verification formulas;
- Noetzli-style algebraic rewrites for complement/absorption, `bvlshr x x`, shifted self-disjoint ORs, and shift/negation distribution.

The solver also has preprocessing shortcuts in `solver.rs` for patterns that are too global for the local builder:

- unsigned successor order contradictions;
- unsigned wraparound SAT witnesses;
- power-of-two sum contradiction patterns;
- shift-one-add contradiction patterns;
- unsigned and signed multiplication-overflow guard proofs;
- log-slicing add/sub, signed/unsigned comparison, and shift equivalence proofs;
- extensional extract/concat candidate contradictions;
- synchronized LFSR reset/injectivity contradictions from Bruttomesso-style state-machine equivalence checks;
- Bruttomesso simple-processor decode/output equivalence contradictions;
- cheap constant/seeded assignment SAT witness detection;
- affine-byte and small explicit assignment SAT witness search, always validated by the evaluator before returning `sat`.

These shortcuts are deliberately conservative. They return conclusive SAT/UNSAT only when the syntactic proof pattern is recognized exactly enough to be sound; otherwise the normal bit-blast/SAT path is used.

## Bit-blasting design

Bit-blasting maps each term to either:

- one Boolean gate for Bool terms; or
- little-endian vectors of Boolean gates for bit-vector terms.

Important design choices:

- The blaster starts from assertions/assumptions/needed model variables and only visits reachable terms.
- Declared variables are included for model extraction when a model is requested.
- The gate arena structurally hashes gates, so repeated Boolean subcircuits share nodes.
- BV circuits are implemented in `circuits.rs` over gate vectors.
- Multiplication by sparse syntactic constants uses a shift-add constant multiplier instead of the full quadratic multiplier when this reduces the generated CNF.

Implemented circuit families include:

- add, sub, negation;
- multiplication;
- unsigned/signed division and remainder;
- signed modulus;
- shifts and rotates;
- extract, concat, zero/sign extension, repeat;
- unsigned/signed comparisons;
- equality and Boolean connectives;
- ITE/select/mux;
- unsigned/signed overflow predicates.

## CNF encoding

The CNF encoder performs Tseitin encoding over the gate graph:

- one SAT variable is allocated per gate output as needed;
- clauses are normalized by sorting/deduplicating literals;
- tautological clauses are skipped;
- deadlines are checked during encoding;
- if a deadline expires, the solver reports `unknown("budget exhausted")` instead of producing a partial answer.

This keeps the SAT interface simple and makes backend switching straightforward.

## SAT backend strategy

SAT backends are selected through `Config::with_sat_backend`:

- `SatBackendKind::Splr`: default production backend;
- `SatBackendKind::Varisat`: alternate pure-Rust backend for experiments/cross-checking;
- `SatBackendKind::Dpll`: internal simple solver retained for fallback/testing.

Backend behavior:

- `splr` is wrapped so known inconsistent/root-conflict errors map to UNSAT.
- `splr` panics are caught and converted to `Unknown`, though the panic hook can still print to stderr.
- budgeted large-CNF `splr` solves can fall back to DPLL to better respect deadlines.
- `varisat` does not support deadlines in this integration, so budgeted `varisat` solves return `Unknown`.
- DPLL is useful for tiny cases and tests, not as the main production backend for large formulas.

## Model extraction

For SAT results with `want_model = true`, the solver maps SAT assignment bits back through `BlastedVariable` records:

- BV variables are reconstructed from little-endian gate bits;
- Bool variables are read from their gate value;
- model values use qfbvsmtrs `ScalarValue` and can be formatted back to SMT-LIB.

If no model is requested, SAT shortcuts may return `sat` without constructing a model. This is used intentionally for cheap witness patterns, including deterministic assignment evaluation, and corpus runs where only `check-sat` is needed.

## Unsat cores

Named unsat cores are supported for named assertions. The current algorithm is deletion-based:

1. solve the full query;
2. for each named assertion, temporarily remove it;
3. keep it removed if the remaining query is still UNSAT;
4. return the minimized set of names that remains necessary.

This is simple and robust but can be expensive because it requires multiple solver calls. It is appropriate for current integration tests and moderate queries; production core extraction for large formulas would benefit from assumption-literal based cores in the SAT backend.

## Optimization

`Command::Minimize` and `Command::Maximize` are implemented by repeated SAT queries using bit-hunt constraints over the target BV. This is solver-backend agnostic and integrates with the existing bit-blast pipeline, but it is not as efficient as a dedicated MaxSMT/optimization engine.

## Server integration

`smt-server` integrates qfbvsmtrs through an adapter:

```text
smt-wire BinaryRequest
        |
        v
qfbvsmtrs wire bridge
        |
        v
qfbvsmtrs Query/Solver
        |
        v
smt-server QueryResult
```

The main server races:

- Z3 backend;
- binbit backend;
- qfbvsmtrs backend.

This lets qfbvsmtrs provide conclusive pure-Rust answers when it can, while existing backends can still win on workloads where qfbvsmtrs is slower or unknown.

## CLI and tooling

The crate provides command-line tools:

- `qfbvsmtrs`: solve one SMT-LIB file; uses a 64 MB worker stack; supports budget/backend/trace environment variables;
- `qfbvsmtrs_stats`: parse/blast/CNF statistics and timing;
- `qfbvsmtrs_bench`: CSV benchmark output for selected cases.

Corpus tooling lives in `scripts/qfbvsmtrs_corpus.py` and supports:

- append-only JSONL reports;
- resumable execution;
- merged latest-by-path baselines;
- skipping known-good files and prior attempt logs;
- family/path filters, including normalized forward-slash matching on Windows reports;
- rerunning only selected result kinds;
- improvement-only official reports via `--record-ok-only` / `--record-kinds`;
- separate `--attempt-report` logs for all attempted cases;
- `--exclude-report` inputs to prevent redundant slow exploratory reruns;
- queue ordering by path, baseline elapsed time, or file size;
- baseline elapsed-time filters for fast/slow segregation;
- wall-clock submission caps with `--max-wall-seconds` while keeping per-file process `--timeout` as the hard worker guardrail.

## Testing and validation design

The validation strategy combines several layers:

1. **Unit and known-answer tests** for specific SMT-LIB and API behaviors.
2. **Circuit-level exhaustive tests** for all 4-bit inputs on many operators.
3. **Randomized circuit property tests** for wider widths.
4. **Tseitin truth-table tests** across SAT backends.
5. **Rust Z3 differential tests** for random formulas and optional corpus slices.
6. **Server integration tests** for binary/text/cached/racing paths.
7. **Fuzz harness** for parser-to-solver pipeline robustness.
8. **Full SMT-LIB corpus runner** for broad conformance/performance triage.

The current strongest evidence is: zero parser/backend errors and zero wrong conclusive answers in the latest merged SMT-LIB corpus reports: `42,554` conclusive matches, `3,622` `unknown`, and `15` process timeouts across `46,191` SMT-LIB 2025 QF_BV files. The main remaining gap is non-conclusive coverage in hard SAT/preprocessing-heavy families.

## Known limitations

- Not production-complete for arbitrary QF_BV corpus workloads yet.
- Latest merged corpus still has `3,622` `unknown` and `15` timeout results under strict/targeted budgets.
- The remaining tail is concentrated in `Sage2` (`2,566`), `asp` (`366`), `20230221-oisc-gurtner` (`106`), `mcm` (`103`), `20210219-Sydr` (`91`), `brummayerbiere3` (`50`, within `91` remaining `brummayerbiere*` cases), `float` (`79`), `log-slicing` (`57`), and smaller arithmetic/BMC families.
- No arrays, floating point, quantifiers, or uninterpreted functions.
- Full no-budget corpus proof is not done.
- Full-corpus Z3 differential testing is not done.
- Long-running fuzz campaign is not done.
- Some preprocessing shortcuts are syntactic and intentionally narrow.
- Unsat-core extraction is deletion-based and can be expensive.
- `varisat` backend currently cannot honor solve deadlines.
- `splr` backend panics are caught as `Unknown`, but panic text may still appear on stderr.

## Design direction

The solver should continue to evolve in three directions:

1. **General word-level simplification**: broader equality propagation, bit-slice reasoning, byte/word packing, polynomial/linear normalization, and range reasoning.
2. **Better SAT scalability**: improved CNF size, incremental assumptions for cores/optimization, and tighter backend timeout integration.
3. **Corpus-driven triage**: keep using merged incremental reports to identify large families, add sound generalizations, and rerun only non-conclusive cases.

This preserves the standalone crate boundary while making qfbvsmtrs increasingly useful as a production-grade pure-Rust backend.
