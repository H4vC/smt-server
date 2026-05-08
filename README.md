# SMT Server

SMT Server lets analysis tools build `QF_BV` formulas with small client libraries and delegate solving or simplification to a separate server.

It targets binary analysis, lifting, symbolic execution, and IR experiments where client projects need bit-vector queries but should avoid embedding solver build systems. A client constructs a flat binary DAG, sends a length-prefixed request, and receives a model, unsat core, optimum value, or simplified expression. The server owns the solver and simplifier integrations.

## Clients

- C++: single C++17 header at `clients/cpp/smt_wire.hpp`.
- Python: dependency-free module at `clients/python/smt_wire.py`.
- Rust: `smt-wire` crate with builders, codecs, validators, and a blocking TCP client.

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

The Python client can be copied into a project or imported by adding `clients/python` to `PYTHONPATH`.

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

## Rust client

```rust
use smt_wire::{ExprBuilder, TcpClient};

let mut b = ExprBuilder::new();
let x = b.bv_var("x", 8).unwrap();
let c = b.bv_const(42, 8).unwrap();
let eq = b.bv_eq(x, c).unwrap();
b.assert(eq).unwrap();
let request = b.build_solve_request(1, 0, true, false).unwrap();

let mut client = TcpClient::connect("127.0.0.1:9123").unwrap();
let response = client.send_binary_request(&request).unwrap();
println!("{:?}", response.envelope.status);
```

## C++ client

The C++ helper is a dependency-free C++17 header:

```cpp
#include "smt_wire.hpp"

smt_wire::Builder b;
auto x = b.bv_var("x", 8);
b.assert_(b.bv_eq(x, b.bv_const(42, 8)));
auto request = b.build_solve_request(1, 0, true, false);

smt_wire::TcpClient client("127.0.0.1", 9123);
auto response = client.send_request(request);
```

On Windows/MSVC the header requests `Ws2_32.lib` automatically. With MinGW, link with `-lws2_32` when using `TcpClient`.

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
python clients/tests/test_python_client.py
python clients/tests/test_live_server.py
```

`clients/tests/test_live_server.py` also exercises the live C++ TCP client when a compiler is available.

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
c++ -std=c++17 -Wall -Wextra -Werror clients/tests/cpp_client_smoke.cpp -o cpp_client_smoke
./cpp_client_smoke
```

## Repository layout

- `crates/smt-wire` — Rust wire-format types, builders, codecs, and validators.
- `crates/qfbvsmtrs` — standalone pure-Rust `QF_BV` bit-blasting solver crate and CLI.
- `crates/smt-server` — TCP server, Rumba simplifier integration, solver backend integration, SMT-LIB frontend.
- `clients/python` — Python single-file client helper.
- `clients/cpp` — C++17 single-header client helper.
- `docs/smt-wire-format-plan.md` — binary wire-format details.
- `docs/qfbvsmtrs-production.md` — qfbvsmtrs production validation gates.
- `docs/qfbvsmtrs-corpus-results.md` — latest SMT-LIB `QF_BV` corpus-run results.
- `docs` — backend notes and evaluation details.
