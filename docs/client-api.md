# Idiomatic client APIs

The Python `python/smt_wire.py` API is the conceptual source of truth for user-facing clients.

## Shape

- `Context` owns an append-only expression DAG, assertions, assumptions, and scopes.
- `BVTerm` and `BoolTerm` are typed handles into one `Context`.
- Terms from different contexts cannot be mixed.
- Handle equality is handle equality. SMT equality remains explicit: `ctx.bv_eq(...)` / `ctx.bool_eq(...)`.
- Serialization, DAG compaction, compacted node IDs, request envelopes, and response payload parsing are hidden behind `Client`.

## Rust

Use `smt_wire::Context`, `BvTerm`, `BoolTerm`, and high-level `Client`:

```rust
use smt_wire::{Client, Context};

let ctx = Context::new();
let x = ctx.bv_var("x", 32)?;
let y = ctx.bv_var("y", 32)?;
let sum = ctx.bv_add(&x, &y)?;
let mba = ctx.bv_add(&ctx.bv_xor(&x, &y)?, &ctx.bv_mul(&ctx.bv_and(&x, &y)?, 2u64)?)?;
ctx.assert_(&ctx.bv_eq(&mba, &sum)?)?;

let mut client = Client::connect("127.0.0.1:9123")?;
let response = client.solve(&ctx)?;
```

Rust keeps protocol internals out of the crate-root client API; normal client code should not build raw node-reference formulas.

## C++

Use `smt_wire::Context`, `BVTerm`, `BoolTerm`, and high-level `Client`:

```cpp
smt_wire::Context ctx;
auto x = ctx.bv_var("x", 32);
auto y = ctx.bv_var("y", 32);
auto mba = (x ^ y) + ((x & y) * 2u);
ctx.assert_(ctx.bv_eq(mba, x + y));

smt_wire::Client client("127.0.0.1", 9123);
auto response = client.solve(ctx);
```

C++ supports operator overloads for the common BV/Bool operations. As in Python, `operator==` is not SMT equality; use `ctx.bv_eq` or `ctx.bool_eq`.

## Low-level protocol internals

The user-facing client APIs intentionally do not expose raw node handles, raw builders, or raw TCP request helpers.

- Rust keeps protocol codecs under `smt_wire::raw` solely for the server crate and conformance tests; they are not re-exported at the crate root.
- C++ keeps protocol machinery in implementation-detail declarations used by `Context` and `Client`; client code should not depend on it.
