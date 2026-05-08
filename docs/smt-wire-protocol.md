# SMT wire protocol reference

`smt-wire` is a little-endian, length-prefixed protocol for stateless QF_BV/Bool queries. The Rust implementation in `crates/smt-wire` is the executable specification; this document records the stable v1 layout and semantics.

## Transport

Every request and response is one frame:

```text
u32_le frame_len
u8[frame_len] frame_payload
```

If `frame_payload` starts with `"SMTQ"`, it is a binary request. Otherwise the payload is treated as one complete UTF-8 SMT-LIB script. Binary responses start with `"SMTR"`; text responses are UTF-8 SMT-LIB output in the same transport frame.

## Expression buffer

A binary request contains a self-contained expression buffer:

```text
Header (32 bytes)
Node array        node_count  * 24 bytes
Child array       child_count * 4 bytes
Blob table        blob_len bytes
```

### Header

| Field | Size | Description |
|---|---:|---|
| `magic` | 4 | `"SMT\0"` |
| `version` | 1 | currently `1` |
| padding | 3 | zero when encoded |
| `node_count` | 4 | number of node records |
| `child_count` | 4 | number of child references |
| `blob_len` | 4 | blob-table byte length |
| reserved | 12 | zero when encoded |

### Node record

| Field | Size | Description |
|---|---:|---|
| `tag` | 1 | operation tag |
| `arity` | 1 | number of child refs |
| `aux_hi` | 2 | tag-specific: extract high bit, extension amount, or select pair count |
| `width` | 4 | BV width; `0` for Bool-producing nodes |
| `aux_lo` | 4 | tag-specific: extract low bit |
| `children` | 4 | start index into the child array |
| `payload` | 8 | inline BV constant or blob reference |

Nodes are topologically ordered. Every child ref of node `i` must point to a node index `< i`.

### Typed node references

Child arrays, roots, targets, and model entries use `u32` typed node references:

| Bits | Meaning |
|---|---|
| bit 31 | sort bit: `0 = BV`, `1 = Bool` |
| bits 0-30 | node-array index |

The sort bit must agree with the referenced node's tag-derived result sort.

### Blob references and constants

A blob reference is encoded as `((offset:u32) << 32) | len:u32` in a `u64` payload. Blobs store UTF-8 symbol names and wide BV constants.

- BV constants with width `<= 64` are stored inline in `payload`.
- BV constants with width `> 64` store exactly `ceil(width / 8)` little-endian bytes in the blob table.
- Unused high bits of non-byte-aligned BV constants are semantically ignored by v1 consumers; encoders should zero them for deterministic output.

Valid BV widths are `1..=65536`.

## Tags

| Value | Tag | Result | Arity / notes |
|---:|---|---|---|
| 0 | `BV_VAR` | BV | blob ref to symbol name |
| 1 | `BV_CONST` | BV | inline or blob constant |
| 2 | `BV_NOT` | BV | 1 |
| 3 | `BV_NEG` | BV | 1 |
| 4 | `BV_AND` | BV | 2 |
| 5 | `BV_OR` | BV | 2 |
| 6 | `BV_XOR` | BV | 2 |
| 7 | `BV_ADD` | BV | 2 |
| 8 | `BV_SUB` | BV | 2 |
| 9 | `BV_MUL` | BV | 2 |
| 10 | `BV_UDIV` | BV | 2; div-by-zero = all ones |
| 11 | `BV_UREM` | BV | 2; rem-by-zero = dividend |
| 12 | `BV_SDIV` | BV | 2; signed, toward zero |
| 13 | `BV_SREM` | BV | 2; sign follows dividend |
| 14 | `BV_SMOD` | BV | 2; sign follows divisor |
| 15 | `BV_SHL` | BV | 2 |
| 16 | `BV_LSHR` | BV | 2 |
| 17 | `BV_ASHR` | BV | 2 |
| 18 | `BV_EXTRACT` | BV | 1; `aux_hi`, `aux_lo` |
| 19 | `BV_CONCAT` | BV | 2; high child then low child |
| 20 | `BV_ZEXT` | BV | 1; `aux_hi` extension amount |
| 21 | `BV_SEXT` | BV | 1; `aux_hi` extension amount |
| 22 | `BV_ITE` | BV | 3; Bool condition, then, else |
| 23 | `BV_SELECT` | BV | `2N+1`; selector/value pairs then default, `aux_hi=N` |
| 24 | `BOOL_TRUE` | Bool | 0 |
| 25 | `BOOL_FALSE` | Bool | 0 |
| 26 | `BOOL_VAR` | Bool | blob ref to symbol name |
| 27 | `BOOL_NOT` | Bool | 1 |
| 28 | `BOOL_AND` | Bool | 2 |
| 29 | `BOOL_OR` | Bool | 2 |
| 30 | `BOOL_IMPLIES` | Bool | 2 |
| 31 | `BV_EQ` | Bool | 2 |
| 32 | `BV_ULT` | Bool | 2 |
| 33 | `BV_ULE` | Bool | 2 |
| 34 | `BV_SLT` | Bool | 2 |
| 35 | `BV_SLE` | Bool | 2 |
| 36 | `UADD_OVF` | Bool | 2 |
| 37 | `SADD_OVF` | Bool | 2 |
| 38 | `USUB_OVF` | Bool | 2 |
| 39 | `SSUB_OVF` | Bool | 2 |
| 40 | `UMUL_OVF` | Bool | 2 |
| 41 | `SMUL_OVF` | Bool | 2 |
| 42 | `NEG_OVF` | Bool | 1 |
| 43 | `SDIV_OVF` | Bool | 2; true iff signed min / -1 |

Variables are identified by `(symbol, sort, width)`, not node identity. Repeated variable nodes with the same name and sort denote the same SMT variable; incompatible re-use of a symbol is invalid.

Common surface operations that are not tags are lowered by clients/frontends, for example `bvugt(a,b)` -> `bvult(b,a)`, rotates -> shifts/or, and Bool equality/xor/ite -> primitive Bool connectives.

## Binary request envelope

A binary frame payload starts with a 32-byte request envelope:

| Field | Size | Description |
|---|---:|---|
| `magic` | 4 | `"SMTQ"` |
| `request_id` | 4 | echoed by the response |
| `command` | 1 | command value |
| `flags` | 1 | request flags |
| `budget_ms` | 4 | solver budget; `0` means unbounded |
| `expr_len` | 4 | expression-buffer byte length |
| `assertion_count` | 2 | assertion root count |
| `named_count` | 2 | number of named assertions among the first assertions |
| `assumption_count` | 2 | assumption root count |
| `target_node` | 4 | target for simplify/optimization; `0` for solve |
| reserved | 4 | must decode as zero |

Payload after the envelope:

1. expression buffer (`expr_len` bytes),
2. assertion roots (`assertion_count * 4` bytes),
3. named assertion blob refs (`named_count * 8` bytes),
4. assumption roots (`assumption_count * 4` bytes).

### Commands

| Value | Command | Meaning |
|---:|---|---|
| 0 | `SOLVE` | satisfiability of assertions under assumptions |
| 1 | `SIMPLIFY` | simplify `target_node` |
| 2 | `MINIMIZE` | optimize BV `target_node` |
| 3 | `MAXIMIZE` | optimize BV `target_node` |

### Request flags

| Bit | Flag | Valid for |
|---:|---|---|
| 0 | `WANT_MODEL` | `SOLVE`, `MINIMIZE`, `MAXIMIZE` |
| 1 | `WANT_CORE` | `SOLVE` |
| 2 | `SIGNED` | `MINIMIZE`, `MAXIMIZE` |

`SIMPLIFY` accepts no flags and no assertions/assumptions. `MINIMIZE`/`MAXIMIZE` require a BV target and do not accept `WANT_CORE`. `SOLVE` requires `target_node = 0`.

## Binary response envelope

A binary response payload starts with a 16-byte response envelope:

| Field | Size | Description |
|---|---:|---|
| `magic` | 4 | `"SMTR"` |
| `request_id` | 4 | copied from the request |
| `status` | 1 | status value |
| `flags` | 1 | response flags |
| `payload_len` | 4 | payload byte length |
| reserved | 2 | must decode as zero |

### Status values

| Value | Status | Meaning |
|---:|---|---|
| 0 | `SIMPLIFIED` | successful simplify response |
| 1 | `SAT` | satisfiable / optimum found |
| 2 | `UNSAT` | unsatisfiable |
| 3 | `UNKNOWN` | inconclusive, often budget exhaustion |
| 4 | `ERROR` | malformed request or backend/frontend error |

### Response flags

| Bit | Flag | Meaning |
|---:|---|---|
| 0 | `HAS_MODEL` | payload contains a model block |
| 1 | `HAS_CORE` | payload contains an unsat-core block |
| 2 | `HAS_EXPR` | payload contains a simplify block |
| 3 | `HAS_VALUE` | payload contains an optimization value |
| 4 | `HAS_MESSAGE` | payload is a UTF-8 diagnostic message |

`ERROR` must use exactly `HAS_MESSAGE`. `UNKNOWN` may have no payload or exactly `HAS_MESSAGE`.

## Response payload blocks

All payload integers are little-endian.

### Scalar value

```text
u32 width          // 0 means Bool
u32 value_len
u8[value_len] value_bytes
```

Bool scalars have `width = 0`, `value_len = 1`, and byte `0` or `1`. BV scalars use little-endian bytes and must zero unused high bits.

### Model block

```text
u32 entry_count
entry[entry_count]

entry:
  u32 node_ref
  ScalarValue value
```

Entries refer to request variable nodes. The value sort/width must match the variable. A server may omit unconstrained variables.

### Unsat core block

```text
u32 name_count
name[name_count]

name:
  u32 name_len
  u8[name_len] utf8_name
```

Names must come from named assertions in the request.

### Simplify block

```text
u32 expr_len
u32 target_node
u8[expr_len] expression_buffer
```

The returned expression buffer is self-contained; `target_node` is the simplified root inside that buffer. `SIMPLIFIED` responses must use exactly `HAS_EXPR`.

### Optimization value block

```text
ScalarValue optimum
[ModelBlock model]    // present iff HAS_MODEL is set
```

`HAS_VALUE` is required for satisfiable optimization responses.

## Command/status matrix

| Command | Status | Payload |
|---|---|---|
| `SOLVE` | `SAT` | empty or `ModelBlock` |
| `SOLVE` | `UNSAT` | empty or `UnsatCoreBlock` |
| `SOLVE` | `UNKNOWN` | empty or message |
| `SIMPLIFY` | `SIMPLIFIED` | `SimplifyBlock` |
| `MINIMIZE` / `MAXIMIZE` | `SAT` | `OptimizationValueBlock` |
| `MINIMIZE` / `MAXIMIZE` | `UNSAT` | empty |
| any | `ERROR` | UTF-8 message |

## Validation requirements

Implementations must reject malformed inputs instead of trusting client data. Important checks include:

- frame length equals the length implied by envelope fields;
- expression length equals `32 + node_count*24 + child_count*4 + blob_len` using checked arithmetic;
- known magic/version/command/status/flag/tag values;
- reserved request/response envelope fields decode as zero;
- child slices, blob refs, roots, targets, and model refs are in bounds;
- child refs are topologically earlier than their parent;
- Bool nodes have width `0`, BV nodes have width `1..=65536`;
- arity and sort/width rules match the tag;
- named assertion refs point to UTF-8 blob strings;
- duplicate named assertions are rejected when `WANT_CORE` is set;
- response flags are compatible with response status;
- returned models/cores/simplified expressions validate against the relevant expression buffer.
