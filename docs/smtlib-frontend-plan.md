# Shared QF_BV SMT-LIB frontend plan

This is a planning document only. It describes a clean path to make SMT-LIB text support correct and reusable without making `qfbvsmtrs` depend on `smt-server` or building a full intermediate AST.

## Motivation

`smt-server` is primarily the binary wire-protocol service. Its SMT-LIB text path was originally a compatibility/porting fallback. It now duplicates a meaningful amount of the standalone `qfbvsmtrs` SMT-LIB frontend, and the two have already diverged in behavior.

The clean long-term fix is a small independent frontend crate used by both projects:

```text
crates/smt-qfbv-smtlib/
```

This crate should parse and semantically lower the supported QF_BV/Bool SMT-LIB subset through a sink trait. It should not own solver logic, wire-format logic, TCP service logic, or a full solver-neutral expression DAG unless one becomes necessary later.

## Design constraints

- Keep `qfbvsmtrs` independent from `smt-server`.
- Keep `smt-server` focused on binary wire protocol and service behavior.
- Avoid a new full AST/IR if a trait sink can directly lower terms.
- Preserve stateless server semantics.
- Allow different command policies for server text frames and standalone CLI scripts.
- Make SMT-LIB semantics correct once, especially for `let`, `define-fun`, annotations, literals, and `get-value` validation.

## Proposed crate responsibility

`crates/smt-qfbv-smtlib` owns:

- yaspar-based SMT-LIB parsing action;
- conversion from parser callbacks to a lightweight command/term walker;
- symbol table, local binding, and macro expansion semantics;
- QF_BV/Bool sort checking;
- indexed literal/operator handling;
- command-policy decisions (`push`/`pop`, `get-value`, unsupported commands);
- lowering through a `QfBvSink` trait.

It does **not** own:

- qfbvsmtrs IR or solver internals;
- smt-wire expression buffers;
- server networking or response framing;
- backend model/core extraction.

## Sink-based design

The frontend parses commands and terms, maintains SMT-LIB scoping state, and calls methods on a caller-provided sink.

A sketch of the trait:

```rust
pub trait QfBvSink {
    type Node: Copy;
    type Error;

    fn bool_const(&mut self, value: bool) -> Result<Self::Node, Self::Error>;
    fn bv_const(&mut self, bytes_le: &[u8], width: u32) -> Result<Self::Node, Self::Error>;

    fn bool_var(&mut self, name: &str) -> Result<Self::Node, Self::Error>;
    fn bv_var(&mut self, name: &str, width: u32) -> Result<Self::Node, Self::Error>;

    fn bool_not(&mut self, x: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_and(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_or(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_implies(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_eq(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_xor(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bool_ite(&mut self, c: Self::Node, t: Self::Node, e: Self::Node) -> Result<Self::Node, Self::Error>;

    fn bv_not(&mut self, x: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_neg(&mut self, x: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_and(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_or(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_xor(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_add(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_sub(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_mul(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_udiv(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_urem(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_sdiv(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_srem(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_smod(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_shl(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_lshr(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_ashr(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;

    fn bv_extract(&mut self, x: Self::Node, hi: u32, lo: u32) -> Result<Self::Node, Self::Error>;
    fn bv_concat(&mut self, high: Self::Node, low: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_zext(&mut self, x: Self::Node, amount: u32) -> Result<Self::Node, Self::Error>;
    fn bv_sext(&mut self, x: Self::Node, amount: u32) -> Result<Self::Node, Self::Error>;
    fn bv_repeat(&mut self, x: Self::Node, count: u32) -> Result<Self::Node, Self::Error>;
    fn bv_rotate_left(&mut self, x: Self::Node, amount: u32) -> Result<Self::Node, Self::Error>;
    fn bv_rotate_right(&mut self, x: Self::Node, amount: u32) -> Result<Self::Node, Self::Error>;
    fn bv_ite(&mut self, c: Self::Node, t: Self::Node, e: Self::Node) -> Result<Self::Node, Self::Error>;

    fn bv_eq(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_ult(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_ule(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_slt(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn bv_sle(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;

    fn uadd_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn sadd_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn usub_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn ssub_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn umul_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn smul_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;
    fn neg_ovf(&mut self, x: Self::Node) -> Result<Self::Node, Self::Error>;
    fn sdiv_ovf(&mut self, a: Self::Node, b: Self::Node) -> Result<Self::Node, Self::Error>;

    fn assert(&mut self, root: Self::Node, name: Option<&str>) -> Result<(), Self::Error>;
    fn assume(&mut self, root: Self::Node) -> Result<(), Self::Error>;
}
```

The final trait should probably group operations or use associated helper traits to avoid an unwieldy public API, but the important idea is direct lowering with no persistent solver-neutral DAG.

## Type/sort handling

The frontend should maintain its own lightweight binding metadata:

```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmtSort {
    Bool,
    Bv(u32),
}

#[derive(Clone, Copy, Debug)]
struct Binding<N> {
    node: N,
    sort: SmtSort,
}
```

This is not a full AST; it is just the information needed for sort checking while lowering.

Term parsing returns `Binding<S::Node>`. The sink is still responsible for its own internal validation.

## Handling SMT-LIB constructs

### Declarations

- `declare-const` and zero-arity `declare-fun` create sink variables.
- Reject or explicitly ignore duplicate declarations according to a policy. Prefer reject for now.
- Store declared names in an environment with sort and node.

### Constants

- `true`/`false` lower to Bool constants.
- `#b...` and `#x...` lower to little-endian bytes plus width.
- `(_ bvN W)` lowers decimal literal `N` modulo width `W` into little-endian bytes.
- Width must be in the supported range.

### `let`

SMT-LIB `let` bindings are simultaneous. Implementation should:

1. evaluate every binding value in the original local environment;
2. only after all values are parsed, extend/shadow locals;
3. parse the body in the extended environment;
4. restore original locals.

Do not use sequential evaluation where later bindings can see earlier bindings from the same `let`.

### `define-fun`

Treat non-recursive `define-fun` as macro expansion:

- Store parameter names/sorts, result sort, and body term representation.
- Expand with a bounded depth, e.g. 64.
- Evaluate arguments in the caller environment.
- Bind parameters simultaneously for body parsing.
- Reject recursive definitions initially.

This does require retaining the body term representation. That can be the parser's lightweight `SExpr` for macro bodies; it does not require a full typed AST for all terms.

### Boolean ops

Support:

- `not`
- `and` / `or` n-ary, including identity cases
- `=>`
- `xor`
- `=` over Bool and BV
- `distinct`
- `ite` over Bool or same-width BV

### Bit-vector ops

Support common QF_BV ops:

- unary: `bvnot`, `bvneg`
- binary/n-ary where SMT-LIB permits: `bvand`, `bvor`, `bvxor`, `bvadd`, `bvmul`
- binary: `bvsub`, divisions/remainders, shifts, comparisons
- derived: `bvugt`, `bvuge`, `bvsgt`, `bvsge`
- structural: `concat`, `extract`, `zero_extend`, `sign_extend`, `repeat`, rotations
- overflow predicates if accepted by the current surface language

The frontend can lower derived operations through sink methods or call primitive sink methods directly.

### Annotations

Support `(! term :named name ...)`:

- For assertions, pass `name` to `sink.assert`.
- For non-assertion terms, ignore unsupported non-semantic attributes but validate pair syntax.

### `check-sat-assuming`

Lower assumptions through `sink.assume` and mark that a check was requested.

### `get-model`, `get-value`, `get-unsat-core`

The frontend should return request metadata separate from sink operations:

```rust
pub struct ParsedScript {
    pub saw_check_sat: bool,
    pub want_model: bool,
    pub want_core: bool,
    pub get_values: Vec<GetValue>,
}

pub enum GetValue {
    Symbol { name: String, sort: SmtSort },
    // Optional future extension:
    // Term { display: String, node: S::Node, sort: SmtSort },
}
```

Initial policy can be `SymbolsOnly`. Under this policy, unknown symbols should be rejected during parsing rather than silently omitted in output.

## Frontend options

Use explicit policies so server and CLI can share implementation but differ in accepted behavior.

```rust
pub struct FrontendOptions {
    pub accepted_logics: AcceptedLogics,
    pub incremental_policy: IncrementalPolicy,
    pub get_value_policy: GetValuePolicy,
    pub require_check_sat: bool,
    pub max_macro_expansion_depth: usize,
}

pub enum AcceptedLogics {
    QfBvOnly,
    QfBvOrAll,
}

pub enum IncrementalPolicy {
    RejectPushPop,
    SimulatePushPop,
}

pub enum GetValuePolicy {
    SymbolsOnly,
    // Future:
    // Terms,
}
```

Suggested defaults:

- `smt-server`: `QfBvOnly`, `RejectPushPop` or `SimulatePushPop` by explicit decision, `SymbolsOnly`, require `check-sat`.
- `qfbvsmtrs` CLI: `QfBvOrAll`, `SimulatePushPop`, `SymbolsOnly`, require `check-sat`.

## Adapter crates/implementations

### qfbvsmtrs adapter

Can live in `qfbvsmtrs` or in a separate helper module:

```rust
struct QfbvSink<'a> {
    builder: &'a mut qfbvsmtrs::Builder,
}
```

`type Node = qfbvsmtrs::TermId`.

The adapter maps sink calls to `qfbvsmtrs::Builder` methods.

### smt-wire adapter

Can live in `smt-server` or possibly `smt-wire` if we want client-side text lowering later:

```rust
struct WireSink<'a> {
    builder: &'a mut smt_wire::ExprBuilder,
}
```

`type Node = smt_wire::NodeRef`.

After parsing, `smt-server` uses the `ParsedScript` metadata plus the builder to produce a `BinaryRequest`.

## Error model

The frontend crate should expose its own error type independent of qfbvsmtrs and smt-wire:

```rust
pub enum FrontendError {
    Parse(String),
    Unsupported(String),
    Invalid { context: &'static str, message: String },
    Sink(String),
}
```

Adapters convert sink-specific errors into `FrontendError::Sink` or use an associated conversion hook.

For user-facing text responses, keep SMT-LIB-friendly formatting in the caller. The frontend should not know whether it is responding over TCP or CLI.

## Implementation phases

### Phase 1: copy and unify parser behavior

- Create `crates/smt-qfbv-smtlib`.
- Move the yaspar action/SExpr code into it.
- Implement the sink trait and a parser/lowerer with qfbvsmtrs semantics as the initial source of truth.
- Keep a lightweight `SExpr` internally for parsed terms and macro bodies.
- Do not build a persistent typed AST.

### Phase 2: qfbvsmtrs consumes the shared frontend

- Add adapter from shared frontend to `qfbvsmtrs::Builder`.
- Replace or wrap `qfbvsmtrs::parse_smt2` with the shared frontend.
- Preserve existing public API.
- Run qfbvsmtrs tests and differential smoke tests.

### Phase 3: smt-server consumes the shared frontend

- Add adapter from shared frontend to `smt_wire::ExprBuilder`.
- Replace `smt-server/src/smtlib.rs` parser/lowerer internals while preserving `handle_text_frame` and response formatting behavior.
- Add regression tests for server-specific policies.

### Phase 4: delete duplicated lowering code

- Remove duplicated parser/lowerer logic from `smt-server` once tests pass.
- Decide whether qfbvsmtrs keeps a thin compatibility wrapper or fully delegates.

## Regression tests to add early

Shared frontend tests:

```smt2
; simultaneous let: expected sat if outer x is #b1
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (= x #b1))
(assert (let ((x #b0) (y x)) (= y #b1)))
(check-sat)
```

```smt2
; unknown get-value symbol: should be rejected, not silently omitted
(set-logic QF_BV)
(declare-const x (_ BitVec 1))
(assert (= x #b1))
(check-sat)
(get-value (y))
```

```smt2
; decimal indexed literal forms
(assert (= x (_ bv10 8)))
(assert (= x (_ bv 10 8)))
```

```smt2
; non-semantic annotations should be accepted if syntax is valid
(assert (! (= x #x00) :named a0 :foo bar))
```

```smt2
; malformed annotations should be rejected, not panic
(assert (! (= x #x00) :named))
```

Also add tests for:

- quoted symbols;
- block comments;
- n-ary equality;
- `distinct`;
- define-fun argument expansion and sort mismatch;
- push/pop policy differences.

## Validation gates

After each phase:

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo test --workspace
python3 python/tests/test_python_client.py
python3 python/tests/test_live_server.py
"/c/Program Files/LLVM/bin/clang++" -std=c++17 -Wall -Wextra -Werror -I cpp/include cpp/tests/cpp_client_smoke.cpp -o /tmp/cpp_client_smoke && /tmp/cpp_client_smoke
```

qfbvsmtrs-specific recommended gates:

```sh
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
```

## Notes on avoiding a full AST

A sink-based frontend still needs some temporary representation because yaspar produces parsed callbacks and because `define-fun` bodies must be retained for later expansion. The goal is to keep this representation lightweight and private:

- `SExpr` or parser term tree for raw syntax;
- `Binding<Node>` for lowered typed terms;
- no public neutral expression DAG;
- no solver-neutral persistent IR.

If future features require repeated transformations independent of sinks, we can revisit a typed AST later. For the current QF_BV use case, direct lowering through a sink is the simplest path.
