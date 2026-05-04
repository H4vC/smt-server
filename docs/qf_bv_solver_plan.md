# Project Plan: Pure-Rust QF_BV SMT Solver via Bit-Blasting

## 1. Project Overview

Build a pure-Rust SMT solver for the **QF_BV** (Quantifier-Free Bit-Vector) logic, targeting symbolic execution and program verification workloads. The solver will parse SMT-LIB 2.7 input using **yaspar**, bit-blast BV expressions into Boolean circuits, Tseitin-encode them into CNF, and solve using a pure-Rust SAT backend.

### 1.1 Scope

**In scope (QF_BV core):**
- Fixed-width bit-vector arithmetic (add, sub, mul, udiv, urem, sdiv, srem)
- Bitwise operations (and, or, xor, not, shift, rotate)
- Comparison (bvult, bvslt, bvuge, bvsge, equals)
- Extraction, concatenation, zero/sign extension
- Boolean connectives over BV predicates (and, or, not, implies, ite)

**Out of scope (for now):**
- Arrays (QF_ABV) — can be added later via read-over-write axioms
- Floating point (QF_BVFP)
- Quantifiers
- Optimization / MaxSMT
- Uninterpreted functions (QF_UFBV)

### 1.2 Dependencies

| Crate | Role | Why this one |
|---|---|---|
| `yaspar` | SMT-LIB 2.7 parsing | Callback-based, no AST allocation unless you want it, SMT-LIB 2.7 compliant |
| `varisat` *or* `rustsat` + `rustsat-batsat` | SAT backend | Pure Rust, cross-platform, no C/C++ toolchain required |
| `rustsat` (encodings) | Cardinality / PB encodings | Optional, useful if you need pseudo-Boolean constraints later |

A secondary SAT backend (e.g. `splr`) should be easy to swap in behind a trait, which is also useful for differential testing.


## 2. Architecture

```
┌─────────────────────────────────────────────────────┐
│                   SMT-LIB Input                     │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│              yaspar (SMT-LIB 2.7 parser)            │
│         callback-driven: ParsingAction trait         │
└────────────────────────┬────────────────────────────┘
                         │  callbacks build:
                         ▼
┌─────────────────────────────────────────────────────┐
│                  BV Expression IR                   │
│   hash-consed DAG of BV terms + Boolean terms       │
│   (Sort-checked, width-annotated)                   │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│              Word-Level Simplifier                  │
│   constant folding, identity removal, extract/      │
│   concat merging, dead-node elimination             │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│                   Bit-Blaster                       │
│   each BV node → vector of Boolean gates            │
│   each BV predicate → single Boolean gate           │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│              Tseitin CNF Encoder                    │
│   gate graph → CNF clauses                          │
│   (fresh variable per gate output)                  │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│                SAT Solver Backend                   │
│   varisat / rustsat-batsat / splr (behind trait)    │
└────────────────────────┬────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────┐
│               Model Extraction                      │
│   SAT assignment → BV constant values               │
│   (reverse bit-mapping per declared variable)       │
└─────────────────────────────────────────────────────┘
```


## 3. Crate / Module Structure

```
qfbv-solver/
├── Cargo.toml
├── crates/
│   ├── qfbv-ir/              # BV expression IR, hash-consing, sorts
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── term.rs        # BvTerm, BoolTerm enums
│   │       ├── arena.rs       # hash-consing arena
│   │       └── sort.rs        # BitVec(n), Bool sort checking
│   │
│   ├── qfbv-frontend/        # yaspar → IR bridge
│   │   └── src/
│   │       ├── lib.rs
│   │       └── action.rs      # impl ParsingAction → builds IR
│   │
│   ├── qfbv-simplify/        # word-level rewrites
│   │   └── src/
│   │       ├── lib.rs
│   │       └── rules.rs       # constant fold, canonicalize, etc.
│   │
│   ├── qfbv-bitblast/        # BV IR → Boolean gate graph
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── gates.rs       # And, Or, Xor, Mux gate types
│   │       ├── circuits.rs    # adder, multiplier, shifter, comparator
│   │       └── blast.rs       # recursive bit-blaster dispatch
│   │
│   ├── qfbv-cnf/             # gate graph → CNF via Tseitin
│   │   └── src/
│   │       ├── lib.rs
│   │       └── tseitin.rs
│   │
│   ├── qfbv-sat/             # SAT backend abstraction + impls
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── backend.rs     # trait SatBackend
│   │       ├── varisat.rs
│   │       └── batsat.rs
│   │
│   └── qfbv-solver/          # top-level orchestration + model extraction
│       └── src/
│           ├── lib.rs
│           ├── solver.rs
│           └── model.rs       # SAT model → BV values
│
├── tests/                     # integration + differential tests
│   ├── smtlib_qfbv/           # SMT-LIB benchmark files (.smt2)
│   ├── unit_bitblast.rs
│   ├── unit_circuits.rs
│   ├── differential.rs
│   └── roundtrip.rs
│
└── tools/
    ├── cli/                   # CLI binary: solve .smt2 files
    └── bench/                 # criterion benchmarks
```


## 4. Implementation Phases

### Phase 1: IR + Frontend (Weeks 1–3)

**Goal:** Parse QF_BV SMT-LIB files into an internal representation.

**4.1.1 — BV Expression IR (`qfbv-ir`)**

Design a hash-consed DAG for BV terms. Every node is interned in an arena and referenced by a `TermId` (u32 index). Each node stores its sort (width for BV, or Bool).

Core term variants:

```rust
enum BvTerm {
    // Leaf nodes
    Const { width: u32, value: BigUint },      // literal bitvec
    Var { width: u32, name: Symbol },           // declared bv const

    // Arithmetic
    BvAdd(TermId, TermId),
    BvSub(TermId, TermId),
    BvMul(TermId, TermId),
    BvUDiv(TermId, TermId),
    BvURem(TermId, TermId),
    BvSDiv(TermId, TermId),
    BvSRem(TermId, TermId),
    BvNeg(TermId),

    // Bitwise
    BvAnd(TermId, TermId),
    BvOr(TermId, TermId),
    BvXor(TermId, TermId),
    BvNot(TermId),
    BvShl(TermId, TermId),
    BvLShr(TermId, TermId),
    BvAShr(TermId, TermId),

    // Structural
    Concat(TermId, TermId),
    Extract { high: u32, low: u32, child: TermId },
    ZeroExtend { extra: u32, child: TermId },
    SignExtend { extra: u32, child: TermId },
    Repeat { count: u32, child: TermId },

    // Conditional (ite with BV result)
    Ite { cond: TermId, then_: TermId, else_: TermId },
}

enum BoolTerm {
    True,
    False,
    BoolVar(Symbol),
    Not(TermId),
    And(Vec<TermId>),
    Or(Vec<TermId>),
    Implies(TermId, TermId),
    Eq(TermId, TermId),           // works for both BV=BV and Bool=Bool
    BvUlt(TermId, TermId),
    BvUle(TermId, TermId),
    BvSlt(TermId, TermId),
    BvSle(TermId, TermId),
    Ite { cond: TermId, then_: TermId, else_: TermId },
}
```

**4.1.2 — yaspar Frontend (`qfbv-frontend`)**

Implement yaspar's `ParsingAction` trait hierarchy to build IR nodes from callbacks. Handle:
- `declare-const`, `declare-fun` (0-arity) for BV variables
- `define-fun` for named subexpressions (inline into IR or store as let-bindings)
- `assert` to collect top-level Boolean constraints
- `check-sat` to trigger solving
- `get-model` / `get-value` for model extraction
- `set-logic QF_BV` validation
- `push` / `pop` for incremental solving (can be stubbed initially)

Since yaspar uses a callback API rather than returning an AST, keep a stack-based builder: as the parser calls back for each subexpression, push intermediate `TermId` values onto a stack, and pop children when a parent node is constructed.

**Deliverable:** can parse any QF_BV `.smt2` file from the SMT-LIB benchmark suite and dump the IR as an S-expression for inspection.


### Phase 2: Bit-Blasting Core (Weeks 4–8)

**Goal:** Lower every BV expression into a vector of Boolean gates, one per bit.

**4.2.1 — Gate Graph (`qfbv-bitblast/gates.rs`)**

```rust
type GateId = u32;
type BitVec = Vec<GateId>;   // bit 0 = LSB

enum Gate {
    // Constants
    True,
    False,

    // Primary input (one per bit of each BV variable)
    Input(u32),   // global input index

    // Boolean gates
    And(GateId, GateId),
    Or(GateId, GateId),
    Xor(GateId, GateId),
    Not(GateId),
    Mux { sel: GateId, t: GateId, f: GateId },   // if sel then t else f
}
```

Store gates in a flat `Vec<Gate>` arena. GateId is the index. During construction, apply structural hashing (detect duplicate gates) and trivial simplifications:
- `And(x, True) → x`, `And(x, False) → False`, `And(x, x) → x`
- `Or(x, True) → True`, `Or(x, False) → x`
- `Not(Not(x)) → x`
- `Xor(x, False) → x`, `Xor(x, x) → False`

**4.2.2 — Circuit Building Blocks (`qfbv-bitblast/circuits.rs`)**

Each BV operation maps to a known circuit. Implement these as functions returning a `BitVec` (the output bits):

| Operation | Circuit | Notes |
|---|---|---|
| `bvadd` | Ripple-carry adder | `n` full-adder cells, discard final carry |
| `bvsub` | `bvadd(a, bvnot(b))` + carry_in=1 | Two's complement |
| `bvmul` | Shift-and-add (Wallace tree optional) | O(n²) gates; Wallace tree for perf later |
| `bvudiv` / `bvurem` | Long division (restoring or non-restoring) | Expensive — O(n²) gates, ~n iterations |
| `bvsdiv` / `bvsrem` | Sign-fixup wrapper around udiv/urem | Negate inputs/outputs based on sign bits |
| `bvneg` | `bvadd(bvnot(x), 1)` | Two's complement negate |
| `bvand/or/xor/not` | Bitwise (per-bit gate) | Trivial |
| `bvshl` | Barrel shifter | log₂(n) stages of mux layers |
| `bvlshr` | Barrel shifter (reverse) | Same structure, opposite direction |
| `bvashr` | Like lshr but fill with sign bit | |
| `concat(a,b)` | Append bit vectors | Zero gates (structural) |
| `extract [h:l]` | Slice bit vector | Zero gates (structural) |
| `zero_extend` | Pad with `False` gates | |
| `sign_extend` | Pad with copies of MSB | |
| `repeat` | Concatenate n copies | |
| `bvult` | Subtraction carry-out | `a < b` ↔ carry-out of `a - b` is 0 |
| `bvslt` | XOR sign bits into unsigned compare | Standard signed comparison circuit |
| `eq` | AND of per-bit XNOR | `a = b` ↔ `∧ᵢ ¬(aᵢ ⊕ bᵢ)` |
| `ite` | Per-bit mux | `mux(sel, then_i, else_i)` for each bit |

**4.2.3 — Top-Level Blaster (`qfbv-bitblast/blast.rs`)**

Walk the BV IR DAG bottom-up. For each `TermId`:
- If it's a BV term of width `n`, produce a `BitVec` of length `n`
- If it's a Bool term, produce a single `GateId`
- Memoize results in a `HashMap<TermId, BitVec>` or `HashMap<TermId, GateId>`

The top-level assertion is a single `GateId` (the conjunction of all asserted Boolean terms). The SAT solver must find an assignment making this gate `True`, or prove it unsatisfiable.


### Phase 3: CNF Encoding + SAT (Weeks 7–10)

**4.3.1 — Tseitin Encoding (`qfbv-cnf`)**

Walk the gate graph. For each gate, introduce a fresh CNF variable and add clauses enforcing the gate semantics:

| Gate | Clauses (var `g` ↔ gate output) |
|---|---|
| `And(a,b)` | `(¬g ∨ a)`, `(¬g ∨ b)`, `(g ∨ ¬a ∨ ¬b)` |
| `Or(a,b)` | `(g ∨ ¬a)`, `(g ∨ ¬b)`, `(¬g ∨ a ∨ b)` |
| `Xor(a,b)` | 4 clauses for `g ↔ a ⊕ b` |
| `Not(a)` | `(g ∨ a)`, `(¬g ∨ ¬a)` |
| `Mux(s,t,f)` | 4–6 clauses for `g ↔ ite(s,t,f)` |
| `True` | unit clause `(g)` |
| `False` | unit clause `(¬g)` |
| `Input(i)` | no clauses (primary input, free variable) |

Add a unit clause asserting the top-level assertion gate to be true.

Only encode gates that are reachable from the assertion root (dead gate elimination via a simple DFS from the root).

**4.3.2 — SAT Backend Trait (`qfbv-sat`)**

```rust
pub enum SatResult {
    Sat(Vec<bool>),      // assignment indexed by CnfVar
    Unsat,
    Unknown,
}

pub trait SatBackend {
    fn new_var(&mut self) -> CnfVar;
    fn add_clause(&mut self, lits: &[Lit]);
    fn solve(&mut self) -> SatResult;
}
```

Implement for `varisat::Solver` and `batsat::Solver`. This lets you swap solvers in tests and benchmarks.

**4.3.3 — Model Extraction (`qfbv-solver/model.rs`)**

When SAT returns `Sat(assignment)`:
1. For each declared BV variable, look up which `Input(i)` gates correspond to its bits
2. Read the assignment for those CNF variables
3. Reconstruct the BV constant value
4. Format as SMT-LIB `get-model` / `get-value` output


### Phase 4: Word-Level Simplification (Weeks 9–12)

**Goal:** Reduce IR size before bit-blasting to shrink the CNF.

**4.4.1 — Constant Folding**
Evaluate any node whose children are all constants. E.g. `bvadd(#x0003, #x0001)` → `#x0004`.

**4.4.2 — Identity / Annihilator Rules**
- `bvadd(x, 0) → x`
- `bvmul(x, 1) → x`, `bvmul(x, 0) → 0`
- `bvand(x, all_ones) → x`, `bvand(x, 0) → 0`
- `bvor(x, 0) → x`, `bvor(x, all_ones) → all_ones`
- `bvxor(x, 0) → x`

**4.4.3 — Extract/Concat Simplification**
- `extract[n-1:0](x)` where `x` has width `n` → `x`
- `extract[h:l](concat(a, b))` → push extract through concat
- `concat(extract[h:m+1](x), extract[m:l](x))` → `extract[h:l](x)` when adjacent

**4.4.4 — Normalization**
- Commutative ops: sort children by TermId for better deduplication
- Double negation: `bvnot(bvnot(x))` → `x`
- Comparison flipping: `bvugt(a, b)` → `bvult(b, a)`

**4.4.5 — Dead Node Elimination**
After simplification, run a reachability pass from assertion roots and drop unreferenced nodes.

Implement as a fixpoint loop: apply all rules until no changes occur. Use a worklist for efficiency.


### Phase 5: Polish + Incremental Solving (Weeks 11–14)

- Support `push` / `pop` with assertion-stack scoping (requires SAT solver assumption-based interface or re-creation)
- Support `get-model`, `get-value`, `exit`, `echo`, `set-info`, `set-option`
- CLI binary: `qfbv-solve input.smt2` → prints `sat` / `unsat` + optional model
- Error messages referencing source positions (yaspar provides `Position` / `Range`)
- Incremental `check-sat` under assumptions using SAT solver assumption literals


## 5. Testing Strategy

Testing is organized in four layers, from unit-level correctness up to whole-solver validation against known-good solvers.

### 5.1 Layer 1 — Unit Tests for Individual Circuits

**What:** Test each circuit function in `qfbv-bitblast/circuits.rs` in isolation: adder, multiplier, comparator, shifter, divider, etc.

**How:** For small widths (4-bit, 8-bit), exhaustively enumerate all input combinations and verify the circuit output matches the expected result computed in Rust natively.

```
For each operation OP in {add, sub, mul, udiv, urem, shl, lshr, ashr, ...}:
    For width in {4, 8}:                          // 4-bit = 256×256 = 65536 pairs
        For all (a, b) in 0..2^width × 0..2^width:
            1. Build a gate graph for OP(a_bits, b_bits)
            2. Tseitin-encode it with a_bits and b_bits forced to constants
            3. Solve with SAT → must be SAT
            4. Extract result bits from the model
            5. Assert result == rust_native_op(a, b)
```

For unary ops (not, neg, extract, extend), enumerate all values of the single operand.

For expensive ops (mul, div at 8-bit = 65536 pairs), this is still fast (well under a second per op). At 16-bit (4B pairs), switch to random sampling (see 5.2).

**Coverage target:** 100% of circuit functions, exhaustive at 4-bit.

### 5.2 Layer 2 — Randomized / Fuzz Testing of Circuits

**What:** For wider widths (16, 32, 64-bit) where exhaustive testing is infeasible, run randomized tests.

**How:**

```
For each operation OP:
    For width in {16, 32, 64}:
        For _ in 0..10_000:
            a, b = random values of `width` bits
            1. Build gate graph, encode, solve
            2. Assert output matches native Rust computation
```

Use `proptest` or `quickcheck` for property-based testing with shrinking. Key properties:

- **Arithmetic identity:** `bvadd(a, 0) == a` for all `a`
- **Commutativity:** `bvadd(a, b) == bvadd(b, a)`
- **Inverse:** `bvsub(bvadd(a, b), b) == a`
- **Negation:** `bvadd(a, bvneg(a)) == 0`
- **Shift-mask:** `bvshl(a, k)` for `k ≥ width` equals 0
- **DeMorgan:** `bvnot(bvand(a, b)) == bvor(bvnot(a), bvnot(b))`
- **Division:** `bvmul(bvudiv(a, b), b) + bvurem(a, b) == a` (when `b ≠ 0`)

### 5.3 Layer 3 — Tseitin Encoding Correctness

**What:** Verify that the Tseitin encoder faithfully preserves the semantics of the gate graph.

**How:**
1. Build small gate graphs (e.g. `And(Xor(a, b), Or(a, c))`) with known truth tables
2. Enumerate all input assignments (feasible for ≤ ~20 inputs)
3. For each assignment, evaluate the gate graph natively (simple recursive eval) to get the expected output
4. Check that the SAT solver under forced inputs agrees: force input variables, add assertion that output variable equals expected value → must be SAT

Also test that forcing the output to the *wrong* value yields UNSAT.

### 5.4 Layer 4 — Differential Testing Against Z3

**What:** The most important end-to-end validation. Run the same `.smt2` files through both our solver and Z3, compare results.

**How:**

```
For each .smt2 file in test suite:
    result_ours = run_our_solver(file)
    result_z3   = run_z3_binary(file)    // via `std::process::Command`

    assert!(result_ours == result_z3)     // sat/unsat must agree
    if sat:
        // Optional: feed our model back into Z3 as assertions
        // to verify the model is valid
```

**Test sources:**
1. **SMT-LIB QF_BV benchmarks** — download from [smtlib.cs.uiowa.edu](https://smtlib.cs.uiowa.edu/benchmarks.shtml). Start with the `QF_BV/20190311-bv-term-small-rw-Noetzli` and `QF_BV/2017-BuchwaldFried` sets (small, fast).
2. **Hand-written regression tests** — edge cases you discover during development: zero-width extracts, division by zero, maximum-width shifts, sign extension of width-1, etc.
3. **Fuzz-generated formulas** — see 5.5.

**Z3 availability:** Differential tests require a `z3` binary on PATH. Gate these behind a cargo feature or environment variable (`DIFFERENTIAL_TESTS=1`) so CI can run them when z3 is installed, and they're skipped otherwise.

### 5.5 Layer 5 — Grammar-Based Fuzzing

**What:** Generate random well-typed QF_BV formulas and test for crashes, panics, and disagreement with Z3.

**How:** Write a random QF_BV formula generator:

```
fn random_bv_formula(rng, max_depth, num_vars, widths) -> String:
    1. Declare N bit-vector variables with random widths from `widths`
    2. Build a random expression tree:
       - At leaves: pick a variable or random constant
       - At internal nodes: pick a random BV operation
         (respecting width constraints — both args same width for
          arithmetic, etc.)
    3. Wrap in (assert ...) (check-sat) (get-model) (exit)
    4. Return as SMT-LIB string
```

Run thousands of generated formulas through both our solver and Z3. Any disagreement is a bug in our solver (Z3 is the oracle). Minimize failing cases with `proptest` shrinking or binary search on the formula AST.

Consider also integrating `cargo-fuzz` / `libfuzzer` targeting the yaspar→IR→bitblast→solve pipeline with arbitrary byte inputs (testing robustness against malformed input).

### 5.6 Layer 6 — Known-Answer Tests (Regression Suite)

Maintain a directory of `.smt2` files with known `sat` / `unsat` answers and (for sat cases) known model values. Run these in CI on every commit. Start with hand-written cases covering:

- Every BV operation individually (e.g. `(assert (= (bvadd #x0F #x01) #x10))`)
- Combinations of 2–3 operations
- Edge cases:
  - Width-1 bit-vectors (effectively Booleans)
  - Maximum-width constants (#xFFFFFFFF for 32-bit)
  - Division / remainder by zero (SMT-LIB defines `bvudiv(x, 0) = #xFF...F` and `bvurem(x, 0) = x`)
  - Shift amounts ≥ width
  - Extract with `high == low` (single bit)
  - Sign extension of a 1-bit value
  - Nested ite expressions

### 5.7 Testing Summary

| Layer | Scope | Method | When to Run |
|---|---|---|---|
| 1. Circuit unit | Individual adder, mul, etc. | Exhaustive 4-bit, exhaustive 8-bit | Every commit |
| 2. Randomized circuit | Wider widths (16/32/64) | proptest, 10k samples | Every commit |
| 3. Tseitin encoding | Gate graph → CNF | Truth table enumeration | Every commit |
| 4. Differential vs Z3 | Whole solver | Compare sat/unsat/model with Z3 | CI (when Z3 available) |
| 5. Fuzzing | Random QF_BV formulas | Grammar-based generation | Nightly / weekly |
| 6. Known-answer | Regression suite | Fixed .smt2 files | Every commit |


## 6. Performance Considerations

### 6.1 Gate Graph Compaction
Structural hashing during gate construction is critical — without it, shared subexpressions generate duplicate gates and the CNF blows up. Use a `HashMap<Gate, GateId>` for deduplication.

### 6.2 Multiplication
Shift-and-add multiplication generates O(n²) gates for n-bit operands. For 64-bit multiply, that's ~4096 full-adder cells → ~12k gates → ~36k CNF clauses. This is manageable. A Booth encoder or Wallace tree compressor can reduce this by ~30–40% but adds implementation complexity — defer until profiling shows multiply is the bottleneck.

### 6.3 Division
Long division is the most expensive operation: O(n²) subtractors, each being an n-bit ripple-carry adder. For 32-bit division, expect ~32 × 32 = ~1024 full-adder cells. This is inherent to bit-blasting division and is why solvers like Bitwuzla apply aggressive word-level rewriting to avoid blasting division when possible (e.g. if the divisor is a constant power of 2, replace with a shift).

### 6.4 CNF Variable Count
A rough budget: each full-adder produces 2 gates (sum, carry). An n-bit add is ~2n gates → ~2n CNF variables + ~6n clauses. A 32-bit formula with 10 additions and 2 multiplications might produce ~50k CNF variables and ~150k clauses — well within what modern SAT solvers handle in milliseconds.

### 6.5 SAT Solver Choice
For the problem sizes typical in symbolic execution (thousands to low millions of CNF variables), all three pure-Rust solvers (varisat, batsat, splr) should be adequate. The SAT backend trait makes benchmarking trivial.


## 7. Division-by-Zero Semantics

SMT-LIB defines specific results for division and remainder by zero:
- `bvudiv(x, 0)` = all-ones (`#xFF...F`)
- `bvurem(x, 0)` = `x`
- `bvsdiv` and `bvsrem` follow from these via sign fixup

The bit-blasting circuit for `bvudiv(a, b)` must handle this: when all bits of `b` are zero, force the quotient to all-ones and the remainder to `a`. Implement with a `b_is_zero` check (NOR of all b-bits) feeding a per-bit mux on the outputs.


## 8. Milestones and Timeline

| Week | Milestone | Exit Criteria |
|---|---|---|
| 1–2 | IR design + hash-consing arena | Can represent all QF_BV terms; sort-checks pass |
| 3 | yaspar frontend integration | Can parse SMT-LIB QF_BV files into IR; dump and round-trip |
| 4–5 | Bit-blasting: bitwise + arithmetic (add, sub, neg) | Layer 1 tests pass for and/or/xor/not/add/sub at 4-bit exhaustive |
| 6–7 | Bit-blasting: mul, div, shifts, comparisons, extract/concat | Layer 1 tests pass for all ops at 4-bit; Layer 2 random tests at 32-bit |
| 8 | Tseitin encoder + SAT integration | Can solve simple hand-written .smt2 files end-to-end |
| 9–10 | Model extraction + full SMT-LIB command support | Layer 4 differential tests passing on small benchmark suites |
| 11–12 | Word-level simplifier | Measurable CNF reduction on benchmarks; no regressions |
| 13–14 | Polish, CLI, incremental solving, CI pipeline | Fuzzing runs (Layer 5) with no crashes; benchmark suite timing baseline |


## 9. Future Extensions (Out of Scope for V1)

- **Arrays (QF_ABV):** add `select` / `store` with read-over-write axiom instantiation (lemma on demand) or eager Ackermann expansion
- **Uninterpreted functions (QF_UFBV):** Ackermann reduction to QF_BV (replace `f(a) = f(b)` with `a = b → fa = fb` for fresh constants `fa, fb`)
- **WASM target:** since all deps are pure Rust, `wasm32-unknown-unknown` should work with minimal effort — test this early
- **Proof production:** emit DRAT or LRAT proofs from the SAT solver and chain them through bit-blasting for certified UNSAT
- **Caching / incremental solving:** for symbolic execution, successive queries often differ by one path constraint — exploit this with assumption-based incremental SAT
