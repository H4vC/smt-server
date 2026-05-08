# SMT Server

SMT Server lets analysis tools build `QF_BV` formulas with small client libraries and delegate solving or simplification to a separate server.

It targets binary analysis, lifting, symbolic execution, and IR experiments where client projects need bit-vector queries but should avoid embedding solver build systems. A client constructs a flat binary DAG, sends a length-prefixed request, and receives a model, unsat core, optimum value, or simplified expression. The server owns the solver and simplifier integrations.

## Clients

- C++: header-only C++17 package under `cpp/`.
- Python: dependency-free package under `python/`, installable with pip's `#subdirectory=python` support.
- Rust: `smt-wire` crate with an idiomatic `Context`/term/`Client` API; protocol internals are isolated for the server.

## Backends

- Solve and optimize: [`z3`](https://docs.rs/z3/latest/z3/), [`binbit`](https://github.com/bint-disasm/binbit), and the standalone `qfbvsmtrs` crate.
- Simplify: [Rumba](https://github.com/thalium/rumba) for supported 64-bit-or-smaller MBA expression islands.
- Text compatibility: SMT-LIB `QF_BV` scripts are parsed into the same binary IR used by binary clients.

The binary protocol is the main API. SMT-LIB support exists for tooling compatibility and test reuse.

## Expression format

Expressions are stored as one contiguous binary buffer:

- nodes are fixed-size records in topological order;
- children are typed integer references into the node array;
- symbol names and wide constants live in a blob table;
- the buffer contains no pointers.

This layout makes requests cheap to copy, send, validate, hash, cache, and replay. The server validates the buffer and translates the flat DAG into backend-specific terms.

Scope is limited to quantifier-free bit-vectors and Booleans. That covers the formulas commonly emitted by lifters, binary-analysis tools, and symbolic-execution engines.

## Build

```sh
cargo build --workspace
```

## Run the server

```sh
cargo run -p smt-server -- 127.0.0.1:9123
```

If no address is provided, the server listens on `127.0.0.1:9123`.

Requests use length-prefixed frames:

```text
u32 little-endian payload length
payload bytes
```

Payload formats:

- binary `SMTQ` request produced by `smt-wire` or one of the clients;
- SMT-LIB script as UTF-8 text.

## Python client example

The Python client can be installed with `pip install 'git+https://github.com/LLVMParty/smt-server.git#subdirectory=python'` or used directly by adding `python/` to `PYTHONPATH`.

```python
import smt_wire as smt

ctx = smt.Context()
x = ctx.bv_var("x", 8)
ctx.assert_(ctx.bv_eq(x, 42))

with smt.Client("127.0.0.1", 9123) as client:
    response = client.solve(ctx)  # want_model=True by default

print(response.status)       # Status.SAT
if response.model is not None:
    for var, value in response.model.items():
        print(f"{var.name} = {hex(int(value))}")

# Dump a self-contained SMT-LIB script for debugging or external solvers.
print(ctx.to_smt2())          # includes check-sat/get-model by default
```

## Simplification example

`SIMPLIFY` requests send one expression root and return a typed term in a fresh result context:

```python
import smt_wire as smt

ctx = smt.Context()
x = ctx.bv_var("x", 64)
target = x + 0

with smt.Client("127.0.0.1", 9123) as client:
    simplified = client.simplify(target)

if simplified.term is not None:
    print(simplified.term.to_smt2())  # full expansion by default
```

`str(term)` still prints a one-layer debug view; use `term.to_smt2(depth=0)` for the same depth-limited form explicitly.

## SMT-LIB text example

A text frame can contain an SMT-LIB script:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x2a))
(check-sat)
(get-value (x))
```

The text frontend supports declarations, assertions, named assertions, `check-sat`, `check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`, `let`, and common bit-vector operations. It rejects stateful incremental commands such as `push` and `pop`.

```python
with smt.Client("127.0.0.1", 9123) as client:
    print(client.smt2(script))
```

The full Python walkthrough is in `python/example.py`.

## Rust client

```rust
use smt_wire::{Client, Context, Status};

let ctx = Context::new();
let x = ctx.bv_var("x", 8).unwrap();
ctx.assert_(&ctx.bv_eq(&x, 42u64).unwrap()).unwrap();

let mut client = Client::connect("127.0.0.1:9123").unwrap();
let response = client.solve(&ctx).unwrap();
println!("{:?}", response.status);
if response.status == Status::Sat {
    if let Some(model) = response.model {
        println!("x = {:?}", model.get_bv(&x));
    }
}
```

A matching Rust walkthrough is in `crates/smt-wire/examples/example.rs`.

## C++ client

The C++ helper is a dependency-free C++17 header:

```cpp
#include <smt_wire/smt_wire.hpp>

smt_wire::Context ctx;
auto x = ctx.bv_var("x", 8);
ctx.assert_(ctx.bv_eq(x, 42u));

smt_wire::Client client("127.0.0.1", 9123);
auto response = client.solve(ctx);
```

A matching C++ walkthrough is in `cpp/example.cpp`. On Windows/MSVC the header requests `Ws2_32.lib` automatically. With MinGW, link with `-lws2_32` when using `Client`.

## Standalone qfbvsmtrs CLI

```sh
cargo run -p qfbvsmtrs -- path/to/query.smt2
```

If no path is supplied, `qfbvsmtrs` reads SMT-LIB from stdin. The default SAT backend is `splr` (CDCL). `varisat` and the internal DPLL solver are selectable through `Config::with_sat_backend`.

Benchmark runner:

```sh
cargo run -p qfbvsmtrs --bin qfbvsmtrs_bench -- path/to/query.smt2
```

## Test

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
cargo check --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
python3 python/tests/test_python_client.py
python3 python/tests/test_live_server.py
cmake -S cpp -B target/cpp-cmake
cmake --build target/cpp-cmake
ctest --test-dir target/cpp-cmake --output-on-failure
```

`python/tests/test_live_server.py` also exercises the live C++ TCP client when a compiler is available.

The default Rumba integration test uses embedded samples. The full CSV dataset test needs Rumba's dataset directory; clone `https://github.com/thalium/rumba` next to this repository or set `SMT_SERVER_RUMBA_DATASET_DIR`. Run the full CSV suite through the binary simplify path with:

```sh
SMT_SERVER_RUMBA_FULL_DATASET=1 cargo test -p smt-server --test rumba_simplify -- --nocapture
```

Optional `qfbvsmtrs` validation gates:

```sh
cargo test -p qfbvsmtrs --test differential_z3
QFBVSMTRS_RANDOM_CIRCUIT_SAMPLES=10000 cargo test -p qfbvsmtrs --test random_circuits
QFBVSMTRS_DIFF_RANDOM=1 cargo test -p qfbvsmtrs --test differential_z3
QFBVSMTRS_SMTLIB_DIR=/path/to/SMT-LIB/QF_BV cargo test -p qfbvsmtrs --test differential_z3
cargo fuzz run smt2_pipeline --manifest-path crates/qfbvsmtrs/fuzz/Cargo.toml
```

Standalone C++ smoke test:

```sh
c++ -std=c++17 -Wall -Wextra -Werror -I cpp/include cpp/tests/cpp_client_smoke.cpp -o cpp_client_smoke
./cpp_client_smoke
```

## Repository layout

- `crates/smt-wire` — Rust high-level client API plus server-side wire-format internals and validators.
- `crates/qfbvsmtrs` — standalone pure-Rust `QF_BV` bit-blasting solver crate and CLI.
- `crates/smt-server` — TCP server, Rumba simplifier integration, solver backend integration, SMT-LIB frontend.
- `python` — Python client package and tests.
- `cpp` — C++17 header-only package, CMake target, and tests.
- `docs/architecture.md` — current crate/server/backend architecture.
- `docs/client-api.md` — Python, C++, and Rust client API notes.
- `docs/smt-wire-protocol.md` — binary wire protocol reference.
- `docs/smtlib-frontend.md` — shared QF_BV SMT-LIB frontend behavior.
- `docs/qfbvsmtrs-design.md` — pure-Rust solver design.
- `docs/qfbvsmtrs-validation.md` — validation gates and latest corpus status.
