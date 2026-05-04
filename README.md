# SMT Server

A small SMT solving server and wire-format toolkit for bit-vector and Boolean formulas.

The project provides:

- a TCP server that accepts either the project binary wire format or SMT-LIB text frames
- native solver backends using the Rust `z3` crate and `binbit`, raced by default
- a Rust wire-format crate (`smt-wire`) with a blocking TCP client
- single-file Python and C++ client helpers for building requests, sending them, and decoding responses

The supported logic is intentionally focused on quantifier-free bit-vectors and Booleans (`QF_BV`).
SMT-LIB input is a compatibility frontend: it is parsed, lowered into the internal wire IR, and then sent to the configured backends.

## Build

```sh
cargo build --workspace
```

## Run the server

```sh
cargo run -p smt-server -- 127.0.0.1:9123
```

If no address is provided, the server listens on `127.0.0.1:9123`.

Requests are sent as length-prefixed frames:

```text
u32 little-endian payload length
payload bytes
```

The payload may be either:

- a binary `SMTQ` request produced by `smt-wire` or one of the clients
- an SMT-LIB script as UTF-8 text

## Python client example

The Python client is a dependency-free single file at `clients/python/smt_wire.py`.
You can copy it into your project or add `clients/python` to `PYTHONPATH`.

```python
import smt_wire as smt

b = smt.Builder()
x = b.bv_var("x", 8)
b.assert_(b.bv_eq(x, b.bv_const(42, 8)))
request = b.build_solve_request(1, want_model=True)

with smt.TcpClient("127.0.0.1", 9123) as client:
    response = client.send_request(request)

print(response.status)       # smt.SAT
print(response.model()[0])
```

## SMT-LIB text example

You can also send an SMT-LIB script as the frame payload:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x2a))
(check-sat)
(get-value (x))
```

The text frontend supports the project’s `QF_BV`/Bool subset, including declarations, assertions, named assertions, `check-sat`, `check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`, `let`, and common bit-vector operations. It does not provide a stateful incremental SMT-LIB session; commands such as `push` and `pop` are rejected.

From Python, send text with the same client:

```python
with smt.TcpClient("127.0.0.1", 9123) as client:
    print(client.send_text(script))
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

The C++ client helper is a dependency-free C++17 header:

```cpp
#include "smt_wire.hpp"

smt_wire::Builder b;
auto x = b.bv_var("x", 8);
b.assert_(b.bv_eq(x, b.bv_const(42, 8)));
auto request = b.build_solve_request(1, 0, true, false);

smt_wire::TcpClient client("127.0.0.1", 9123);
auto response = client.send_request(request);
```

On Windows/MSVC the header requests `Ws2_32.lib` automatically. With MinGW, link with `-lws2_32` if you use `TcpClient`.

## Test

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
python clients/tests/test_python_client.py
python clients/tests/test_live_server.py   # also exercises the live C++ TCP client when a compiler is available
```

A standalone C++ smoke test is also available:

```sh
c++ -std=c++17 -Wall -Wextra -Werror clients/tests/cpp_client_smoke.cpp -o cpp_client_smoke
./cpp_client_smoke
```

## Repository layout

- `crates/smt-wire` — Rust wire-format types, builders, codecs, and validators
- `crates/smt-server` — TCP server, backend integration, SMT-LIB frontend
- `clients/python` — Python single-file client helper
- `clients/cpp` — C++17 single-header client helper
- `docs/smt-wire-format-plan.md` — detailed binary wire-format plan
- `docs` — backend notes and evaluation details
