# qfbvsmtrs design

`qfbvsmtrs` is a standalone pure-Rust solver for quantifier-free bit-vector formulas. It is also integrated into `smt-server` as `QfbvsmtrsBackend`, but the solver crate does not depend on the server crate.

## Pipeline

```text
Native builder / SMT-LIB / smt-wire bridge
        |
        v
qfbvsmtrs Query IR
        |
        v
builder simplification + solver shortcut engine
        |
        v
reachable-term bit-blasting
        |
        v
structurally hashed Boolean gate graph
        |
        v
Tseitin CNF
        |
        v
SAT backend: splr / varisat / internal DPLL
        |
        v
SolveResult: sat/model, unsat/core, optimum, or unknown
```

The conventional bit-blast/SAT path is the sound fallback. The solver also contains conservative word-level rewrites and pattern-specific shortcut proofs for common benchmark families; those shortcuts return conclusive answers only when their syntactic proof obligations are met, otherwise the query falls through to bit-blasting.

## Crate layout

Core crate: `crates/qfbvsmtrs`.

| File / directory | Responsibility |
|---|---|
| `lib.rs` | public exports and optional `wire` feature |
| `config.rs` | budgets, cancellation token, SAT backend choice, shortcut mode |
| `error.rs` | solver-local `Error` / `Result` |
| `ir.rs` | hash-consed typed arena, `TermId`, `Sort`, `NodeKind` |
| `query.rs` | assertions, assumptions, commands, optimization target, output requests |
| `builder.rs` | native builder API and eager local simplification |
| `frontend.rs` | adapter from shared SMT-LIB frontend into qfbvsmtrs IR and SMT-LIB response formatting |
| `wire.rs` | optional `smt-wire` bridge for server integration |
| `gates.rs` | Boolean gate arena with structural hashing |
| `circuits.rs` | bit-vector circuits over Boolean gates |
| `blast.rs` | reachable IR to gate graph |
| `cnf.rs` | Tseitin encoder and CNF data structures |
| `sat.rs` | SAT backend dispatch and adapters |
| `model.rs` | model values and SAT-assignment reconstruction |
| `solver.rs` | top-level solve/optimize/core orchestration |
| `solver/shortcuts/` | global proof/witness shortcuts grouped by family |
| `eval.rs` | evaluator used to validate cheap SAT witnesses |
| `simplify.rs` | simplification module hook/documentation |

The shared SMT-LIB parser is in `crates/smt-qfbv-smtlib`; qfbvsmtrs only supplies a sink adapter.

## Public entry points

SMT-LIB text:

```rust
let result = qfbvsmtrs::solve_smt2(script, &qfbvsmtrs::Config::default())?;
```

Native builder:

```rust
let mut b = qfbvsmtrs::Builder::new();
let x = b.bv_var("x", 8)?;
let y = b.bv_const(42, 8)?;
let eq = b.bv_eq(x, y)?;
b.assert(eq)?;
let query = b.finish()?;
let result = qfbvsmtrs::Solver::new(Default::default()).solve(&query)?;
```

Server bridge, behind the `wire` feature:

```rust
let query = qfbvsmtrs::query_from_wire(&binary_request)?;
```

## IR and frontend

The IR is a sorted, hash-consed DAG:

- every node has a `Sort::Bool` or `Sort::Bv(width)`;
- construction validates sort and width constraints;
- structurally identical nodes share one `TermId`;
- the arena is append-only and therefore naturally topological.

The SMT-LIB frontend supports the QF_BV/Bool subset documented in `docs/smtlib-frontend.md`. It lowers directly through the builder so parsed scripts receive the same eager simplification as native API users.

## Simplification and shortcuts

Local builder rewrites include:

- Bool constants, idempotence, tautology/contradiction pairs, double negation;
- BV constant folding for arithmetic, bitwise, shift, extract, concat, extension, repeat, rotate, and comparison ops;
- identities/annihilators such as `x + 0`, `x * 1`, `x & 0`, `x | 0`, `x ^ 0`;
- structural extract/concat and extension simplifications;
- associative/commutative canonicalization for selected arithmetic;
- selected algebraic rewrites for shifted products/adds, disjoint additions, polynomial/equality normalization, and common bit-hack identities.

The global shortcut engine handles patterns that are not local rewrites, including assignment witnesses, direct equality/disequality contradictions, arithmetic guard proofs, division/remainder fixed points, extensional extract/concat candidates, log-slicing equivalences, LFSR/state-machine patterns, simple-processor equivalences, Favaro MBA samples, polynomial packs, and popcount/bit-hack families.

SAT witness shortcuts are validated with the internal evaluator before returning `sat`.

## Bit-blasting and CNF

Bit-blasting starts from reachable assertions/assumptions and requested model variables. Bool terms become one gate; BV terms become little-endian gate vectors. The gate arena structurally hashes gates so repeated subcircuits share nodes.

Implemented circuits cover:

- add/sub/negation/multiplication;
- unsigned and signed division/remainder/modulus;
- shifts, rotates, extract, concat, zero/sign extension, repeat;
- unsigned/signed comparisons and equality;
- Bool connectives, ITE/select/mux;
- unsigned/signed overflow predicates.

The Tseitin encoder allocates SAT variables for reachable gate outputs, normalizes clauses, skips tautologies, and checks deadlines during encoding.

## SAT backends

`Config::with_sat_backend` selects the backend:

- `SatBackendKind::Splr`: default standalone/backend choice for unbudgeted solves;
- `SatBackendKind::Varisat`: alternate pure-Rust backend for experiments and cross-checking;
- `SatBackendKind::Dpll`: internal polling solver useful for tests, small cases, and budgeted in-process server fallback.

Backend adapters turn backend errors, panics, or budget exhaustion into `Unknown` rather than wrong conclusive answers. SAT assignments are validated against the emitted CNF before a conclusive `sat` is returned.

## Models, unsat cores, and optimization

For SAT results with `want_model`, SAT assignment bits are reconstructed into qfbvsmtrs `ScalarValue`s for requested variables.

Named unsat cores are deletion-based: solve the full query, try removing named assertions one at a time, and keep only assertions needed to preserve UNSAT. This is robust but can be expensive for large core requests.

`MINIMIZE` and `MAXIMIZE` use repeated SAT checks with bit-hunt constraints over the target BV. This keeps optimization backend-agnostic but is not a dedicated MaxSMT engine.

## Known limitations

- QF_BV/Bool only: no arrays, floating point, quantifiers, or uninterpreted functions.
- The solver is sound under the tested contract but not production-complete for every SMT-LIB QF_BV benchmark; see `docs/qfbvsmtrs-validation.md` for the current corpus tail.
- Some shortcut families are intentionally syntactic and narrow.
- Unsat-core extraction is deletion-based.
- `varisat` is mainly a cross-checking/experimental backend in this integration.
- Very large generated formulas may require the CLI/server worker stack used by the repository entry points.
