# qfbvsmtrs core/shortcut separation plan

This document is intended as a hand-off plan for a future agent. It proposes a clean way to separate the qfbvsmtrs core solver from benchmark-specific shortcuts/pattern recognizers, while preserving the existing `smt-server` integration and keeping `qfbvsmtrs` usable as an independent standalone solver.

## Context

The workspace currently has three main crates:

- `smt-wire`: binary wire-format types, validation, builders, codecs, and Rust TCP client.
- `smt-server`: TCP server, binary protocol dispatch, server backends, cache/racing, and a POC SMT-LIB text frontend.
- `qfbvsmtrs`: standalone pure-Rust QF_BV solver with SMT-LIB frontend, IR/builder, simplification, bit-blasting, CNF encoding, SAT backends, model extraction, and many shortcut recognizers.

The intended ownership boundary is:

- `smt-server` is primarily about the binary wire protocol and service behavior.
- `qfbvsmtrs` should remain a standalone solver project.
- SMT-LIB text support is useful, but should not force `qfbvsmtrs` to depend on `smt-server`.

`qfbvsmtrs/src/solver.rs` has grown into a mix of:

1. core solve orchestration;
2. bit-blast + CNF + SAT solving;
3. optimization and named-core extraction;
4. general semantic shortcuts;
5. corpus/benchmark-family-specific pattern recognizers.

The result works and is heavily tested, but it is hard to audit. A future production claim should be able to say which part is the trusted core and which part is optional heuristic acceleration.

## Current important files

### Core-ish components

- `crates/qfbvsmtrs/src/ir.rs`
  - Arena, `TermId`, sorts, node kinds, width validation.
- `crates/qfbvsmtrs/src/builder.rs`
  - Query construction and many eager semantic-preserving rewrites.
- `crates/qfbvsmtrs/src/query.rs`
  - Query shape and command metadata.
- `crates/qfbvsmtrs/src/gates.rs`
  - Boolean gate arena.
- `crates/qfbvsmtrs/src/circuits.rs`
  - Bit-vector circuits over gates.
- `crates/qfbvsmtrs/src/blast.rs`
  - Bit-blasting from word-level IR to gates.
- `crates/qfbvsmtrs/src/cnf.rs`
  - Tseitin CNF encoding.
- `crates/qfbvsmtrs/src/sat.rs`
  - SAT backend selection (`splr`, `varisat`, internal DPLL).
- `crates/qfbvsmtrs/src/model.rs`
  - Model reconstruction from SAT assignments.
- `crates/qfbvsmtrs/src/eval.rs`
  - Query evaluation under assignments; useful for validating SAT shortcuts.
- `crates/qfbvsmtrs/src/config.rs`
  - Solver configuration.

### Mixed core + shortcuts

- `crates/qfbvsmtrs/src/solver.rs`
  - Core solve path and many shortcut recognizers are interleaved.

Shortcut entry points currently called before bit-blasting include:

- `has_direct_equality_disequality_contradiction`
- `has_polynomial_definition_contradiction`
- `has_structural_definition_contradiction`
- `has_unsigned_successor_contradiction`
- `has_shift_one_add_contradiction`
- `has_distinct_power_of_two_sum_contradiction`
- `has_unsigned_multiplication_overflow_guard_contradiction`
- `has_signed_division_multiply_overflow_guard_contradiction`
- `has_simple_processor_equivalence_contradiction`
- `has_extensional_candidate_contradiction`
- `has_synchronized_lfsr_contradiction`
- `has_log_slicing_shift_contradiction`
- `has_log_slicing_comparison_contradiction`
- `has_log_slicing_adder_contradiction`
- `has_urem_remainder_fixed_point_contradiction`
- `has_favaro_mba_mul_contradiction`
- `has_yurichev_popcount_contradiction`
- `has_brummayer_popcount_contradiction`

SAT/witness shortcuts include:

- `has_unsigned_successor_wraparound_witness`
- `has_linear_slice_sat_witness`
- `has_affine_byte_sat_witness`
- `has_small_explicit_assignment_witness`
- `has_constant_assignment_witness`

### Frontends/adapters

- `crates/qfbvsmtrs/src/frontend.rs`
  - Standalone SMT-LIB frontend. More complete than the server POC frontend.
- `crates/qfbvsmtrs/src/wire.rs`
  - Optional `smt-wire` adapter behind the `wire` feature.
- `crates/smt-server/src/smtlib.rs`
  - Server SMT-LIB POC frontend. It currently duplicates logic from qfbvsmtrs and has diverged.

## Goals

1. Make the trusted core solver path easy to audit:
   - parse/lower query;
   - optional semantic-preserving rewrites;
   - bit-blast;
   - CNF encode;
   - SAT solve;
   - model extraction;
   - optimization via repeated core solves;
   - named core extraction via repeated core solves.
2. Move conclusive shortcuts into a clearly optional layer.
3. Keep existing behavior initially: no intentional performance regressions and no removed corpus shortcuts.
4. Keep `qfbvsmtrs` independent from `smt-server`.
5. Provide a route to share SMT-LIB frontend behavior without duplicating semantic lowering bugs.
6. Improve soundness confidence by requiring shortcut validation/certification where practical.

## Non-goals for the first refactor

- Do not implement a new SAT solver.
- Do not change the binary wire protocol.
- Do not remove any existing shortcut during the mechanical extraction phase.
- Do not rewrite all SMT-LIB support at once.
- Do not claim production completeness solely from this refactor.

## Proposed crate/module structure

There are two viable approaches. Prefer Approach A if a slightly larger workspace split is acceptable.

### Approach A: split into crates

Add independent crates:

```text
crates/qfbvsmtrs-core/
crates/qfbvsmtrs-shortcuts/
crates/smt-qfbv-smtlib/        # optional, for shared SMT-LIB frontend reuse
crates/qfbvsmtrs/              # facade/CLI crate, preserves current public package name
```

#### `qfbvsmtrs-core`

Owns the trusted solving pipeline:

```text
src/
  lib.rs
  config.rs
  error.rs
  ir.rs
  builder.rs
  query.rs
  model.rs
  eval.rs
  gates.rs
  circuits.rs
  blast.rs
  cnf.rs
  sat.rs
  solver.rs
  optimize.rs        # optional extraction from solver.rs
  core_extract.rs    # optional extraction from solver.rs
```

The core solver should expose:

```rust
pub struct Solver { ... }
pub struct SolveResult { ... }
pub enum SolveStatus { Sat, Unsat, Unknown, Ok }

impl Solver {
    pub fn solve(&mut self, query: &Query) -> Result<SolveResult>;
    pub fn solve_without_shortcuts(&mut self, query: &Query) -> Result<SolveResult>;
}
```

Core may keep cheap, obviously semantic-preserving builder rewrites, but those should stay in `builder.rs` and be documented as normalization/simplification, not benchmark shortcuts.

#### `qfbvsmtrs-shortcuts`

Depends on `qfbvsmtrs-core`. Owns optional conclusive recognizers and SAT witness shortcuts.

Suggested layout:

```text
src/
  lib.rs
  engine.rs
  direct_eq.rs
  polynomial.rs
  structural.rs
  order.rs
  overflow_guards.rs
  bit_hacks/
    mod.rs
    popcount.rs
    brummayer.rs
    favaro_mba.rs
  log_slicing.rs
  extensional.rs
  witnesses.rs
  certificates.rs
```

Expose a small interface:

```rust
pub struct ShortcutEngine {
    passes: Vec<Box<dyn ShortcutPass>>,
}

pub enum ShortcutOutcome {
    NoMatch,
    Unsat(UnsatJustification),
    Sat(SatJustification),
    Unknown(String),
}

pub trait ShortcutPass: Send + Sync {
    fn name(&self) -> &'static str;
    fn run(&self, query: &Query, ctx: &ShortcutContext<'_>) -> Result<ShortcutOutcome>;
}
```

The facade `qfbvsmtrs` crate can enable this by default:

```rust
pub fn solve_query(query: &Query, config: Config) -> Result<SolveResult> {
    if config.shortcuts_enabled {
        if let Some(result) = qfbvsmtrs_shortcuts::try_solve(query, &config)? {
            return Ok(result);
        }
    }
    qfbvsmtrs_core::Solver::new(config).solve(query)
}
```

#### `smt-qfbv-smtlib` (optional but recommended)

A new frontend crate independent of both `smt-server` and `qfbvsmtrs`.

It should own SMT-LIB parsing and QF_BV semantic lowering policy, with adapters supplied by consumers.

Two possible designs:

1. Parse to a neutral QF_BV AST/command stream, then each consumer lowers to its own builder.
2. Parse and lower through a trait implemented by each consumer.

A trait-based design can reduce duplication:

```rust
pub trait QfBvSink {
    type Node: Copy;
    type Error;

    fn bool_const(&mut self, value: bool) -> Result<Self::Node, Self::Error>;
    fn bool_var(&mut self, name: &str) -> Result<Self::Node, Self::Error>;
    fn bv_var(&mut self, name: &str, width: u32) -> Result<Self::Node, Self::Error>;
    fn bv_const(&mut self, bytes: &[u8], width: u32) -> Result<Self::Node, Self::Error>;
    fn bv_add(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    // ... all supported QF_BV/Bool ops ...
    fn assert(&mut self, root: Self::Node, name: Option<&str>) -> Result<(), Self::Error>;
    fn assume(&mut self, root: Self::Node) -> Result<(), Self::Error>;
}
```

Policy options should let `smt-server` remain stateless while `qfbvsmtrs` CLI can support push/pop:

```rust
pub struct FrontendOptions {
    pub accepted_logics: AcceptedLogics,        // QF_BV only vs QF_BV|ALL
    pub incremental_policy: IncrementalPolicy, // RejectPushPop vs SimulatePushPop
    pub get_value_policy: GetValuePolicy,      // SymbolsOnly vs Terms
    pub require_check_sat: bool,
}
```

This avoids `qfbvsmtrs` depending on `smt-server` and prevents duplicated SMT-LIB semantic bugs.

### Approach B: split into modules only

If crate churn is undesirable, keep one `qfbvsmtrs` crate but reorganize modules:

```text
src/
  solver/
    mod.rs           # public Solver orchestration
    core.rs          # bit-blast/CNF/SAT core
    optimize.rs
    core_extract.rs
    shortcuts/
      mod.rs
      direct_eq.rs
      polynomial.rs
      structural.rs
      bit_hacks.rs
      witnesses.rs
```

This is easier mechanically but weaker as an architectural boundary. It is still better than the current monolithic `solver.rs`.

## Recommended migration plan

### Phase 0: freeze behavior with tests

Before moving code, add targeted tests that pin current behavior:

- Existing full suite: `cargo test --workspace`.
- qfbvsmtrs known-answer fixtures.
- A small test per shortcut family if not already covered.
- SAT shortcut tests should verify returned `sat` models when requested, or verify that shortcut is bypassed when a model is required and cannot be produced.
- Add a no-shortcuts config test once the config exists.

Add config knobs without changing default behavior:

```rust
pub enum ShortcutMode {
    Enabled,
    Disabled,
    ValidateSatWitnesses,
    Audit,
}
```

Initial default: `Enabled`, to preserve performance.

### Phase 1: extract the core solve path

Move core orchestration into a clean internal function:

```rust
fn solve_core_once_with_deadline(
    query: &Query,
    want_model: bool,
    deadline: Option<Instant>,
    config: &Config,
) -> Result<SolveResult>
```

This function should do only:

1. deadline check;
2. bit-blast;
3. CNF encode;
4. SAT solve;
5. validate SAT assignment against CNF (already done in `sat.rs`);
6. build model if requested.

No pattern recognizers should be called from this function.

Then make `Solver::solve` call:

1. shortcut engine if enabled;
2. core solve fallback;
3. named-core extraction if needed;
4. optimization path if command is optimize.

### Phase 2: introduce `ShortcutEngine`

Move the current pre-blast shortcut calls into a registry in the same order as today.

Initial behavior can be exactly equivalent:

```rust
for pass in default_unsat_passes() {
    if pass.run(query, ctx)? == ShortcutOutcome::Unsat(...) {
        return Ok(SolveResult::unsat());
    }
}

for pass in default_sat_witness_passes() {
    if pass.run(query, ctx)? == ShortcutOutcome::Sat(...) {
        return Ok(SolveResult::sat(None));
    }
}
```

Important: keep the existing order for the first extraction to minimize behavior changes.

### Phase 3: add shortcut validation hooks

For SAT shortcuts:

- Prefer returning an explicit assignment/model hint.
- Validate the hint with `eval.rs` before returning `sat`.
- If `want_model` is true, either construct a full `Model` or skip the shortcut and fall back to core.

Suggested shape:

```rust
pub enum SatJustification {
    FullModel(Model),
    AssignmentHint(AssignmentHint),
    ExistenceOnly { family: &'static str },
}
```

Rules:

- `FullModel` must validate against the query before returning.
- `AssignmentHint` should be expanded and evaluated before returning.
- `ExistenceOnly` may return `sat` only when no model is requested; it should be considered audit debt.

For UNSAT shortcuts:

- Initially keep differential/known-answer coverage.
- Add an `UnsatJustification` enum so each pass explains what it matched.
- For general algebraic shortcuts, build small local checkers where possible.
- For benchmark-recognition shortcuts, keep them isolated and clearly named.

Suggested shape:

```rust
pub enum UnsatJustification {
    EqualityDisequalityConflict { terms: Vec<TermId> },
    PolynomialConflict { details: String },
    StructuralConflict { details: String },
    RecognizedBitHack { family: &'static str, details: String },
}
```

The core API does not need a full proof object yet, but the structure makes future proof/certificate checking possible.

### Phase 4: move shortcut families into files

Suggested mapping from current `solver.rs`:

| Target file | Current content |
|---|---|
| `direct_eq.rs` | Direct equality/disequality collection and union-find conflict. |
| `polynomial.rs` | Polynomial definitions, pack equivalence, polynomial eval. |
| `structural.rs` | Structural signatures and structural definition conflicts. |
| `order.rs` | Unsigned successor/order contradictions and wraparound witness. |
| `overflow_guards.rs` | Multiplication/division overflow guard contradictions. |
| `log_slicing.rs` | Log-slicing shift/comparison/adder recognizers. |
| `bit_hacks/popcount.rs` | Yurichev/Brummayer popcount recognizers. |
| `bit_hacks/favaro_mba.rs` | Favaro MBA multiplication contradiction. |
| `witnesses.rs` | Linear slice, affine byte, small explicit assignment, constant assignment SAT witnesses. |
| `extensional.rs` | Extensional candidate and synchronized LFSR recognizers if not better grouped elsewhere. |

Each file should expose one or more `ShortcutPass` implementations and keep helper functions private.

### Phase 5: feature flags and public API

Add config and feature controls:

```rust
pub struct Config {
    pub sat_backend: SatBackendKind,
    pub budget: Option<Duration>,
    pub shortcut_mode: ShortcutMode,
}
```

Cargo features if split into crates:

- `default = ["smt2", "shortcuts", "splr"]`
- `shortcuts = ["dep:qfbvsmtrs-shortcuts"]`
- `wire = ["dep:smt-wire"]`

The existing package name `qfbvsmtrs` should remain the stable facade for downstream users.

### Phase 6: frontend reuse cleanup

The server POC frontend currently duplicates qfbvsmtrs frontend logic. This has already caused divergence risk. A clean long-term path is:

1. Add independent `smt-qfbv-smtlib` crate.
2. Move yaspar action/sexpr parsing there.
3. Implement correct SMT-LIB semantics once, including simultaneous `let` bindings.
4. Add adapter from `smt-qfbv-smtlib` to `qfbvsmtrs::Builder`.
5. Add adapter from `smt-qfbv-smtlib` to `smt_wire::ExprBuilder`.
6. Make `smt-server` text path use the shared frontend with server-specific options:
   - stateless request;
   - reject or explicitly simulate push/pop according to policy;
   - validate `get-value` symbols/terms;
   - keep binary request id as 0 for text path unless protocol evolves.

This keeps both projects independent while eliminating duplicated lowering bugs.

## Shortcut soundness policy

Adopt this policy after the mechanical move:

1. The core bit-blast path is the reference implementation.
2. Any shortcut that returns `sat` should either:
   - produce a model validated by `eval.rs`, or
   - only return `sat` when no model is requested and be marked as `ExistenceOnly`.
3. Any shortcut that returns `unsat` should:
   - be isolated by family;
   - have targeted known-answer tests;
   - have differential Z3 tests where possible;
   - eventually provide a checkable justification.
4. In `ShortcutMode::Audit`, run shortcut and core when budget permits and report disagreements.
5. In production-sensitive callers, allow disabling shortcuts entirely.

## Suggested validation gates after each phase

Required:

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
python3 python/tests/test_python_client.py
python3 python/tests/test_live_server.py
"/c/Program Files/LLVM/bin/clang++" -std=c++17 -Wall -Wextra -Werror -I cpp/include cpp/tests/cpp_client_smoke.cpp -o /tmp/cpp_client_smoke && /tmp/cpp_client_smoke
```

Recommended qfbvsmtrs-specific gates:

```sh
QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000 cargo test -p qfbvsmtrs --test random_circuits
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
```

If corpus data is available:

```sh
QFBVSMTRS_SMTLIB_DIR=/path/to/SMT-LIB/QF_BV cargo test -p qfbvsmtrs --test differential_z3
```

For shortcut refactors, also run a targeted corpus rerun over families associated with the moved shortcut file.

## Open design questions

1. Should `qfbvsmtrs-core` be a separately publishable crate, or an internal workspace crate used only by the facade?
2. Should shortcuts be enabled by default in the facade? Initial answer: yes, to preserve current performance; expose `ShortcutMode::Disabled`.
3. How strong must UNSAT certificates be? Initial answer: justifications + tests first; proof-checking later.
4. Should server text support lower directly to `smt-wire`, or should it call qfbvsmtrs text parsing for all text frames? Preferred long-term answer: shared independent frontend crate with adapters.
5. How much of `Builder`'s eager rewriting belongs in core? Recommendation: keep semantic-preserving local rewrites in core builder; move conclusive benchmark recognizers out.

## First concrete task for the next agent

Do **not** begin by moving thousands of lines. Start with these small, reviewable PR-sized changes:

1. Add `ShortcutMode` to `qfbvsmtrs::Config`, defaulting to enabled.
2. Extract a private `solve_core_once_with_deadline` from `Solver::solve_once_with_deadline` that has no shortcuts.
3. Add a test showing `ShortcutMode::Disabled` still solves a small sat/unsat query via the core path.
4. Add a `shortcuts` module containing only the current top-level shortcut call order; do not yet split helpers into many files.
5. Run the full required validation gates.

After that baseline is green, split one shortcut family at a time into separate files.
