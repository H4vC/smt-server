# Client APIs

The user-facing clients expose the same model: a `Context` owns an append-only typed DAG, `BVTerm` and `BoolTerm` are lightweight handles into that context, and `Client` hides request serialization and response parsing.

## Common semantics

- Terms from different contexts cannot be mixed.
- Handle equality is not SMT equality. Use `ctx.bv_eq(...)` or `ctx.bool_eq(...)`.
- Python and C++ overload common BV/Bool operators for ergonomics; Rust uses explicit `Context` methods.
- Integer operands are coerced to bit-vector constants using the width of the bit-vector operand.
- `push`/`pop` are client-side assertion-scope operations; the server still receives one complete stateless request.
- Serialization, DAG compaction, request envelopes, TCP framing, and response payload parsing are implementation details behind `Client`.
- When no address is passed, clients read `SMT_SERVER_ADDRESS=<host>:<port>` and otherwise fall back to `127.0.0.1:9123`.

The full side-by-side walkthroughs are:

- Python: `python/example.py`
- C++: `cpp/tests/example.cpp`
- Rust: `crates/smt-wire/examples/example.rs`

## Python

Install from this repository:

```sh
pip install 'git+https://github.com/LLVMParty/smt-server.git#subdirectory=python'
```

Or use directly from a checkout:

```sh
PYTHONPATH=python python3 python/example.py
```

Minimal usage:

```python
import smt_wire as smt

ctx = smt.Context()
x = ctx.bv_var("x", 8)
ctx.assert_(ctx.bv_eq(x, 42))

with smt.Client() as client:
    response = client.solve(ctx)

print(response.status)
if response.model is not None:
    for var, value in response.model.items():
        print(var.name, hex(int(value)))
```

## C++

The C++ client is header-only C++17 and exposes the CMake target `smt_wire::smt_wire` from `cpp/CMakeLists.txt`:

```cmake
add_subdirectory(path/to/smt-server/cpp)
target_link_libraries(my_tool PRIVATE smt_wire::smt_wire)
```

Minimal usage:

```cpp
#include <smt_wire/smt_wire.hpp>

smt_wire::Context ctx;
auto x = ctx.bv_var("x", 8);
ctx.assert_(ctx.bv_eq(x, 42u));

smt_wire::Client client;
auto response = client.solve(ctx);
```

On Windows/MSVC the header requests `Ws2_32.lib` automatically. With MinGW, link with `-lws2_32` when using `Client`.

## Rust

Use the `smt-wire` crate in this workspace:

```rust
use smt_wire::{Client, Context, Status};

let ctx = Context::new();
let x = ctx.bv_var("x", 8)?;
ctx.assert_(&ctx.bv_eq(&x, 42u64)?)?;

let mut client = Client::connect_default()?;
let response = client.solve(&ctx)?;
if response.status == Status::Sat {
    if let Some(model) = response.model {
        println!("x = {:?}", model.get_bv(&x));
    }
}
```

Protocol internals remain available under `smt_wire::raw` for the server and conformance tests, but normal client code should use `Context`, typed terms, and `Client`.
