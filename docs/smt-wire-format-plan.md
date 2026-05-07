# SMT Wire Format & Protocol — Design Plan

## Overview

A binary format for representing QF_BV + Bool SMT expressions that requires no deserialization. Clients construct expressions in-place in a flat buffer and send it over the wire to a solver server. The server translates to backend-specific ASTs/terms (Z3, binbit, Bitwuzla, or another backend), races configured backends, and returns results in the same format. A secondary text path accepts standard SMT-LIB 2.6 input for tooling compatibility.

Design priorities: client simplicity (single-file libraries in C++/Python/Rust), server cacheability (stateless request/response), and zero-copy reads (validate a byte buffer, then traverse it without materializing a separate AST).

---

## 1. Architecture

### System topology

Clients are lightweight, header-only or single-file libraries. They build a flat expression DAG, collect assertions and assumptions, serialize to a contiguous byte buffer, and send it. They do not link against any solver. The server is a shared service that owns the solver backends.

### Client responsibilities

- DAG construction (append-only buffer building)
- Push/pop scope tracking (snapshot and restore assertion list length)
- Hash-consing during construction (optional but recommended; `(tag, child0, child1) → NodeId` map)
- Client-side lowering of convenience operations (see §4)
- Mutual exclusivity assertions (emit pairwise `not(and(si, sj))` — pure DAG construction)
- Variable aliasing (rewrite references at construction time, never hits the wire)
- Constant folding and concretization probes (`try_const_value` is a client-side check)
- DAG compaction before send (reachability walk, renumber, emit only live nodes)

### Server responsibilities

- Binary format decoding (validate and traverse the buffer — zero-copy where the implementation language permits it safely)
- SMT-LIB text parsing (build the same internal IR)
- Backend translation (walk node array bottom-up, build backend-specific ASTs/terms)
- Parallel backend dispatch (race configured backends, return first conclusive result)
- Caching (`hash(request) → response` for deduplication and replay)
- Model extraction and response formatting

### Stateless protocol

Every request is self-contained. No sessions, no server-side state between requests. Push/pop is client-side bookkeeping over the assertion list. This enables:

- Request-level caching (pure function from query to answer)
- Deduplication of concurrent identical queries
- Horizontal scaling (any server instance can handle any request)
- Backend comparison and correctness oracles
- Replay and regression testing

The tradeoff is that learned clauses don't persist across requests. The server can mitigate this internally (solver pooling, warm-start heuristics) without exposing it in the protocol.

---

## 2. Buffer Layout

A request's expression buffer is four contiguous sections:

```
┌────────────────┬──────────────────┬───────────────────┬────────────────┐
│ Header (32B)   │ Node array       │ Child array       │ Blob table     │
│                │ N × 24B          │ M × 4B            │ variable       │
└────────────────┴──────────────────┴───────────────────┴────────────────┘
```

### Header (32 bytes)

| Field            | Size | Description                                      |
|------------------|------|--------------------------------------------------|
| `magic`          | 4B   | `"SMT\0"`                                        |
| `version`        | 1B   | Format version, currently `1`                    |
| `_pad`           | 3B   | Reserved; encoders should write zero, decoders ignore |
| `node_count`     | 4B   | Number of nodes in the node array                |
| `child_count`    | 4B   | Number of entries in the child array              |
| `blob_len`       | 4B   | Byte length of the blob table                    |
| `_reserved`      | 12B  | Future use; encoders should write zero, decoders ignore |

All multi-byte fields are little-endian. This applies to expression buffers, request/response envelopes, transport frame lengths, and response payloads.

### Node record (24 bytes)

| Field       | Size | Description                                                        |
|-------------|------|--------------------------------------------------------------------|
| `tag`       | 1B   | Node kind (see §3)                                                 |
| `arity`     | 1B   | Number of children in the child array                              |
| `aux_hi`    | 2B   | Tag-specific: extract high bound, extend amount, select pair count |
| `width`     | 4B   | Bitvector width (0 for Bool nodes)                                 |
| `aux_lo`    | 4B   | Tag-specific: extract low bound                                    |
| `children`  | 4B   | Start index into the child array                                   |
| `payload`   | 8B   | Literal value (≤64-bit) or blob reference `((offset:u32) << 32) \| len:u32` |

Nodes are laid out in construction order (topological / bottom-up). Node `i` is at byte offset `32 + i × 24`. Children of any node are at indices `[children .. children + arity)` in the child array. For strict validation, every child reference must point to a node index lower than the parent node index.

### Child array

Flat array of `uint32_t` node references. Each reference is a typed ID: bit 31 encodes sort (0 = BV, 1 = Bool), bits 0–30 encode the node index. This provides structural sort-checking without a separate sort table.

### Blob table

Contiguous byte region storing variable-length data: symbol names (UTF-8) and wide literal values (little-endian bytes). Referenced from node payloads via offset and length.

---

## 3. Node Tags

44 tags total: 24 BV-producing tags, 7 Bool leaf/connective tags, 5 BV comparison tags, and 8 overflow-predicate tags. Every tag maps directly to the server's backend translation layer. Backend adapters should use direct backend API calls where available; if a backend lacks a feature needed by a request, that backend is not eligible for that request.

### Bitvector leaves

| Tag            | Arity | Aux                  | Payload                                           |
|----------------|-------|----------------------|----------------------------------------------------|
| `BV_VAR`       | 0     | —                    | Blob ref to symbol name                            |
| `BV_CONST`     | 0     | —                    | Inline value if width ≤ 64; blob ref otherwise     |

### Bitvector unary

| Tag       | Arity |
|-----------|-------|
| `BV_NOT`  | 1     |
| `BV_NEG`  | 1     |

### Bitvector binary (operands must be same width)

| Tag        | Arity | Notes                               |
|------------|-------|--------------------------------------|
| `BV_AND`   | 2     |                                      |
| `BV_OR`    | 2     |                                      |
| `BV_XOR`   | 2     |                                      |
| `BV_ADD`   | 2     |                                      |
| `BV_SUB`   | 2     |                                      |
| `BV_MUL`   | 2     |                                      |
| `BV_UDIV`  | 2     | div-by-zero = all ones               |
| `BV_UREM`  | 2     | rem-by-zero = dividend               |
| `BV_SDIV`  | 2     | toward zero                          |
| `BV_SREM`  | 2     | sign follows dividend                |
| `BV_SMOD`  | 2     | sign follows divisor                 |
| `BV_SHL`   | 2     | shift amount same width as operand   |
| `BV_LSHR`  | 2     | logical shift right                  |
| `BV_ASHR`  | 2     | arithmetic shift right, sign-fills   |

### Bitvector structural

| Tag          | Arity | Aux                                        |
|--------------|-------|--------------------------------------------|
| `BV_EXTRACT` | 1     | `aux_hi` = high bit, `aux_lo` = low bit    |
| `BV_CONCAT`  | 2     | first child is high bits, second is low     |
| `BV_ZEXT`    | 1     | `aux_hi` = number of bits to extend by      |
| `BV_SEXT`    | 1     | `aux_hi` = number of bits to extend by      |

### Bitvector conditional

| Tag          | Arity    | Aux                     | Children layout                                |
|--------------|----------|-------------------------|------------------------------------------------|
| `BV_ITE`     | 3        | —                       | `[condition(Bool), then(BV), else(BV)]`        |
| `BV_SELECT`  | 2N + 1   | `aux_hi` = N (pairs)    | `[s0, v0, s1, v1, …, sN-1, vN-1, default]`    |

`BV_SELECT` has first-match semantics: value of the first true selector wins, otherwise default. Selectors are Bool refs, values and default are BV refs of matching width.

### Bool leaves

| Tag          | Arity | Payload                    |
|--------------|-------|----------------------------|
| `BOOL_TRUE`  | 0     | —                          |
| `BOOL_FALSE` | 0     | —                          |
| `BOOL_VAR`   | 0     | Blob ref to symbol name    |

### Bool connectives

| Tag            | Arity |
|----------------|-------|
| `BOOL_NOT`     | 1     |
| `BOOL_AND`     | 2     |
| `BOOL_OR`      | 2     |
| `BOOL_IMPLIES` | 2     |

### Comparisons (BV × BV → Bool)

| Tag      | Arity |
|----------|-------|
| `BV_EQ`  | 2     |
| `BV_ULT` | 2     |
| `BV_ULE` | 2     |
| `BV_SLT` | 2     |
| `BV_SLE` | 2     |

### Overflow predicates (→ Bool)

| Tag          | Arity | Notes                        |
|--------------|-------|-------------------------------|
| `UADD_OVF`  | 2     |                               |
| `SADD_OVF`  | 2     |                               |
| `USUB_OVF`  | 2     |                               |
| `SSUB_OVF`  | 2     |                               |
| `UMUL_OVF`  | 2     |                               |
| `SMUL_OVF`  | 2     |                               |
| `NEG_OVF`   | 1     |                               |
| `SDIV_OVF`  | 2     | true iff INT_MIN / -1         |

### Tag numbering

Tags are assigned sequentially starting from 0. New tags are appended at the end. v1 assigns:

| Value | Tag            |
|------:|----------------|
| 0     | `BV_VAR`       |
| 1     | `BV_CONST`     |
| 2     | `BV_NOT`       |
| 3     | `BV_NEG`       |
| 4     | `BV_AND`       |
| 5     | `BV_OR`        |
| 6     | `BV_XOR`       |
| 7     | `BV_ADD`       |
| 8     | `BV_SUB`       |
| 9     | `BV_MUL`       |
| 10    | `BV_UDIV`      |
| 11    | `BV_UREM`      |
| 12    | `BV_SDIV`      |
| 13    | `BV_SREM`      |
| 14    | `BV_SMOD`      |
| 15    | `BV_SHL`       |
| 16    | `BV_LSHR`      |
| 17    | `BV_ASHR`      |
| 18    | `BV_EXTRACT`   |
| 19    | `BV_CONCAT`    |
| 20    | `BV_ZEXT`      |
| 21    | `BV_SEXT`      |
| 22    | `BV_ITE`       |
| 23    | `BV_SELECT`    |
| 24    | `BOOL_TRUE`    |
| 25    | `BOOL_FALSE`   |
| 26    | `BOOL_VAR`     |
| 27    | `BOOL_NOT`     |
| 28    | `BOOL_AND`     |
| 29    | `BOOL_OR`      |
| 30    | `BOOL_IMPLIES` |
| 31    | `BV_EQ`        |
| 32    | `BV_ULT`       |
| 33    | `BV_ULE`       |
| 34    | `BV_SLT`       |
| 35    | `BV_SLE`       |
| 36    | `UADD_OVF`     |
| 37    | `SADD_OVF`     |
| 38    | `USUB_OVF`     |
| 39    | `SSUB_OVF`     |
| 40    | `UMUL_OVF`     |
| 41    | `SMUL_OVF`     |
| 42    | `NEG_OVF`      |
| 43    | `SDIV_OVF`     |

A client that encounters a future unknown tag can skip it using `arity` and `children` — it knows how many children to skip even without understanding the semantics. A v1 server that must solve or simplify the formula rejects unknown tags with `ERROR`.

---

## 4. Client-Side Lowering

The following operations are common in SMT-LIB and binary analysis but are **not** format tags. Clients lower them to primitives during construction. This keeps the tag set small and the server simple.

| Surface operation          | Client lowering                            |
|----------------------------|--------------------------------------------|
| `bv_ne(a, b)`             | `bool_not(bv_eq(a, b))`                   |
| `bv_ugt(a, b)`            | `bv_ult(b, a)` (swap operands)            |
| `bv_uge(a, b)`            | `bv_ule(b, a)`                            |
| `bv_sgt(a, b)`            | `bv_slt(b, a)`                            |
| `bv_sge(a, b)`            | `bv_sle(b, a)`                            |
| `bv_rotate_left(x, k)`    | `bv_or(bv_shl(x, k), bv_lshr(x, w-k))`  |
| `bv_rotate_right(x, k)`   | `bv_or(bv_lshr(x, k), bv_shl(x, w-k))`  |
| `bool_xor(a, b)`          | `bool_not(bool_eq(a, b))` or `and`/`or`/`not` |
| `bool_ite(c, t, e)`       | `bool_or(bool_and(c, t), bool_and(bool_not(c), e))` |
| `bool_eq(a, b)`           | XNOR: `bool_and(bool_or(a, bool_not(b)), bool_or(bool_not(a), b))` |
| `assert_mutex(sels)`      | pairwise `assert(bool_not(bool_and(si, sj)))` |

---

## 5. Typed Node References

Node IDs are `uint32_t` with the high bit encoding the sort:

| Bit 31 | Meaning   | Index range     |
|--------|-----------|-----------------|
| 0      | BV node   | 0 – 2^31 - 1   |
| 1      | Bool node | 0 – 2^31 - 1   |

All entries in the child array use this encoding. This provides structural sort-checking at construction time and during server validation without a separate sort table or per-node sort field. The underlying node array is shared — the sort bit is metadata on the *reference*, not the node.

---

## 6. Constants and Wide Literals

Constants are encoded with a width-dependent strategy:

- **Width ≤ 64 bits**: value is stored inline in the 8-byte `payload` field. No blob table access needed. The value is interpreted little-endian as an unsigned integer; bits above `width` are semantically ignored by v1 consumers. Canonical encoders should zero bits above `width` for deterministic hashing and cache keys.

- **Width > 64 bits**: `payload` encodes a blob table reference as `(offset << 32) | byte_length`. The blob table stores the value as little-endian bytes, exactly `ceil(width / 8)` bytes long. This handles SSE (128-bit), AVX (256-bit), AVX-512 (512-bit), and arbitrary-precision constants uniformly. If `width` is not a multiple of 8, unused high bits in the final byte are semantically ignored by v1 consumers. Canonical encoders should zero them for deterministic hashing and cache keys.

The client API exposes this as two constructors: a common-case one taking a machine integer, and a wide one taking a byte/limb array. The branching is internal.

---

## 7. Widths

Bitvector widths are `uint32_t`. Valid range: `1..65536`. Width 0 indicates a Bool node (which doesn't use the width field meaningfully). Widths are not restricted to powers of two — `extract` routinely produces odd widths (7-bit flag slices, 3-bit ARM immediates, etc.).

Width constraints are validated by the client during construction. The server re-validates on decode but should not need to reject well-formed clients.

---

## 8. Wire Protocol

### Transport

TCP or Unix domain socket. Every request and response is carried inside a single length-prefixed transport frame:

```
u32_le frame_len
u8[frame_len] frame_payload
```

For a binary request, `frame_payload` begins with the 32-byte request envelope whose first four bytes are `"SMTQ"`. For a binary response, `frame_payload` begins with the 16-byte response envelope whose first four bytes are `"SMTR"`. For a text request, `frame_payload` is the complete SMT-LIB script bytes and therefore does not begin with `"SMTQ"`.

The protocol is request/response with pipelining via `request_id`. Responses may arrive out of order, but each response is still exactly one length-prefixed frame.

### Request envelope

| Field              | Size | Description                                                 |
|--------------------|------|--------------------------------------------------------------|
| `magic`            | 4B   | `"SMTQ"`                                                    |
| `request_id`       | 4B   | Client-assigned, echoed in response                          |
| `command`          | 1B   | `SOLVE`, `SIMPLIFY`, `MINIMIZE`, `MAXIMIZE`                  |
| `flags`            | 1B   | `WANT_MODEL`, `WANT_CORE`, `SIGNED` (for min/max)           |
| `budget`           | 4B   | Millisecond timeout; 0 = unbounded                           |
| `expr_len`         | 4B   | Byte length of the expression buffer                         |
| `assertion_count`  | 2B   | Number of assertion root IDs                                 |
| `named_count`      | 2B   | How many of the first assertions are named                   |
| `assumption_count` | 2B   | Number of assumption root IDs                                |
| `target_node`      | 4B   | For SIMPLIFY: expression root to simplify; for MINIMIZE/MAXIMIZE: BV node to optimize; 0 otherwise |
| `_pad`             | 4B   | Reserved; encoders should write zero, decoders ignore         |

Total: 32 bytes.

Following the header:

1. Expression buffer (`expr_len` bytes) — self-contained: header + nodes + children + blob table
2. Assertion root IDs (`assertion_count × 4B`) — Bool node refs into the expression buffer
3. Named assertion string refs (`named_count × 8B`) — each is `(blob_offset: u32, blob_len: u32)` pointing into the expression buffer's blob table
4. Assumption root IDs (`assumption_count × 4B`) — Bool node refs, temporary for this solve call only

The binary request frame length must equal `32 + expr_len + assertion_count*4 + named_count*8 + assumption_count*4`. `named_count` must be less than or equal to `assertion_count`; the first `named_count` assertion roots are the named assertions. `SOLVE` uses assertions/assumptions and requires `target_node = 0`. `SIMPLIFY` accepts a single target expression, requires `target_node` to be a valid BV or Bool node ref, and uses no assertions or assumptions. For `MINIMIZE`/`MAXIMIZE`, `target_node` must be a valid BV node ref.

### Commands

| Command      | Description                                                    |
|--------------|----------------------------------------------------------------|
| `SOLVE`      | Check satisfiability of assertions under assumptions           |
| `SIMPLIFY`   | Simplify the expression rooted at `target_node` and return a simplified expression buffer plus new root |
| `MINIMIZE`   | Find minimum value of `target_node` under constraints          |
| `MAXIMIZE`   | Find maximum value of `target_node` under constraints          |

Command values are fixed for v1:

| Value | Command    |
|------:|------------|
| 0     | `SOLVE`    |
| 1     | `SIMPLIFY` |
| 2     | `MINIMIZE` |
| 3     | `MAXIMIZE` |

Request flag bits are fixed for v1:

| Bit | Flag         | Meaning                                      |
|----:|--------------|----------------------------------------------|
| 0   | `WANT_MODEL` | Return a model when the result is `SAT`      |
| 1   | `WANT_CORE`  | Return an unsat core when the result is `UNSAT` |
| 2   | `SIGNED`     | Use signed comparison for min/max            |

`MINIMIZE`/`MAXIMIZE` perform the bit-hunt optimization loop server-side, avoiding multiple round-trips. The `SIGNED` flag controls whether the optimization uses unsigned or signed comparison.

In v1, `budget` is always a millisecond timeout. `budget = 0` means unbounded. The timeout is applied to backend solving after successful request decode/validation and IR translation. For backend racing, each backend receives the same timeout budget. If the timeout is exhausted before a conclusive answer, the response is `UNKNOWN`. Conflict-count/resource budgets are deferred to a future protocol extension rather than multiplexed through this field.

### Response envelope

| Field          | Size | Description                                         |
|----------------|------|------------------------------------------------------|
| `magic`        | 4B   | `"SMTR"`                                             |
| `request_id`   | 4B   | Echoed from request                                  |
| `status`       | 1B   | `OK`, `SAT`, `UNSAT`, `UNKNOWN`, `ERROR`             |
| `flags`        | 1B   | Response flags                                       |
| `payload_len`  | 4B   | Byte length of the payload                            |
| `_pad`         | 2B   | Reserved; encoders should write zero, decoders ignore |

Total: 16 bytes. The binary response frame length must equal `16 + payload_len`.

Status values are fixed for v1:

| Value | Status    |
|------:|-----------|
| 0     | `OK`      |
| 1     | `SAT`     |
| 2     | `UNSAT`   |
| 3     | `UNKNOWN` |
| 4     | `ERROR`   |

Response flag bits are fixed for v1:

| Bit | Flag          | Meaning                                            |
|----:|---------------|----------------------------------------------------|
| 0   | `HAS_MODEL`   | Payload contains a model block                     |
| 1   | `HAS_CORE`    | Payload contains an unsat-core block               |
| 2   | `HAS_EXPR`    | Payload contains a simplified expression block     |
| 3   | `HAS_VALUE`   | Payload contains an optimization value block       |
| 4   | `HAS_MESSAGE` | Payload contains a UTF-8 diagnostic message        |

`OK` is used for successful non-satisfiability commands such as `SIMPLIFY`. `UNKNOWN` means the millisecond timeout was exhausted or the backend returned an inconclusive result. This is distinct from `UNSAT` — the client must treat it as inconclusive. A `UNKNOWN` result from a bounded solve is safe to retry with a larger timeout.

### Response payloads

All payload integers are little-endian. Payload fields are tightly packed with no alignment padding. Unless stated otherwise, `OK`/`SAT`/`UNSAT`/`UNKNOWN` responses with no requested data have `payload_len = 0`.

A response with `status = ERROR` always uses the error payload, independent of command:

```
u8[payload_len] message_utf8
```

`HAS_MESSAGE` must be set. The message is not NUL-terminated.

#### Scalar value block

Used by model entries and optimization results.

```
u32 width
u32 value_len
u8[value_len] value_bytes
```

Rules:

- Bool values use `width = 0`, `value_len = 1`, and `value_bytes[0]` is `0` or `1`.
- BV values use `width > 0`, `value_len = ceil(width / 8)`, and little-endian bytes.
- For BV widths not divisible by 8, unused high bits in the final byte must be zero.

#### Model block

Returned for `SAT` when `WANT_MODEL` is set. `HAS_MODEL` must be set.

```
u32 entry_count
entry[entry_count]

entry:
  u32 node_ref
  ScalarValue value
```

`node_ref` is the typed node reference of a `BV_VAR` or `BOOL_VAR` node from the request expression buffer. Bool variables are encoded with the Bool sort bit set. BV variables use the BV sort bit. The scalar value width must match the referenced variable's sort and width. The server may return only variables relevant to the formula; clients must treat absent variables as unconstrained.

#### Unsat core block

Returned for `UNSAT` when `WANT_CORE` is set. `HAS_CORE` must be set.

```
u32 name_count
name[name_count]

name:
  u32 name_len
  u8[name_len] name_utf8
```

Names are copied into the response, so the payload is self-contained. Each name must match one of the request's named assertions. Named assertion names should be unique in the request when `WANT_CORE` is set; if duplicates are present, the server may reject the request with `ERROR`.

#### Simplify block

Returned by `SIMPLIFY` on success. `status = OK` means the simplification completed successfully, and `HAS_EXPR` must be set.

```
u32 expr_len
u32 target_node
u8[expr_len] expression_buffer
```

The expression buffer is a complete expression buffer using the same layout as requests. `target_node` is the typed BV or Bool root of the simplified expression inside the returned expression buffer. This block intentionally uses a compact header rather than reusing the request envelope; clients can reuse the expression-buffer parser, then evaluate or display the returned `target_node`.

#### Optimization value block

Returned by `MINIMIZE`/`MAXIMIZE` when the constraints are satisfiable. `status = SAT` and `HAS_VALUE` must be set.

```
ScalarValue optimum
[ModelBlock model]   // present only when WANT_MODEL was set
```

The returned value is the BV bit pattern of the optimum and its width must match `target_node`. The request's `SIGNED` flag only controls the ordering used to find that optimum. If `WANT_MODEL` is set, `HAS_MODEL` must also be set and the model block immediately follows the scalar value block.

#### Command/status matrix

| Command | Status    | Payload                                                                  |
|---------|-----------|--------------------------------------------------------------------------|
| `SOLVE` | `SAT`     | empty, or `ModelBlock` if `WANT_MODEL`                                   |
| `SOLVE` | `UNSAT`   | empty, or `UnsatCoreBlock` if `WANT_CORE`                                |
| `SOLVE` | `UNKNOWN` | empty                                                                    |
| `SIMPLIFY` | `OK`  | `SimplifyBlock`                                                           |
| `SIMPLIFY` | `ERROR`/`UNKNOWN` | error payload for `ERROR`, empty for `UNKNOWN`                  |
| `MINIMIZE`/`MAXIMIZE` | `SAT` | `OptimizationValueBlock`                                         |
| `MINIMIZE`/`MAXIMIZE` | `UNSAT` | empty                                                            |
| `MINIMIZE`/`MAXIMIZE` | `UNKNOWN` | empty                                                          |
| any     | `ERROR`   | error payload                                                            |

### Pipelining

The `request_id` field allows multiple in-flight requests over a single connection. Responses may arrive out of order. This is important for symbolic execution workloads that fire hundreds of small feasibility probes.

---

## 9. SMT-LIB Text Support

### Routing

The server accepts both binary and text on the same port. The transport frame is always length-prefixed. After reading a frame, the first 4 bytes of the frame payload distinguish the format: if they match `"SMTQ"`, parse a binary request; otherwise, treat the whole frame payload as one complete SMT-LIB text script (which normally starts with `(`, `;`, or whitespace).

### Scope

The text frontend accepts a single, self-contained SMT-LIB 2.6 script per request. The script is parsed in its entirety, translated to the internal IR, and executed as one query. There is no multi-command session — `push`/`pop` and incremental interaction are not supported on the text path. If a script contains `push`/`pop`, the server returns an error. This keeps the text path fully stateless, identical to the binary path.

Supported commands:

- `set-logic` — accepted, validated as QF_BV, otherwise no-op
- `declare-const`, `declare-fun` (0-arity only)
- `define-const`, `define-fun` (0-arity only, inline-expanded)
- `assert`, including `(! expr :named name)` for named assertions
- `check-sat`, `check-sat-assuming`
- `get-model`, `get-value`
- `get-unsat-core`
- `exit`
- `let` bindings (inline-expanded during parsing)

Not supported: `push`, `pop`, arrays, quantifiers, non-zero-arity `define-fun`, `reset`, uninterpreted sorts/functions.

### Internal pipeline

The SMT-LIB parser builds the same internal IR (node array + child array + blob table) that the binary decoder produces. All downstream code — caching, backend translation, response formatting — is format-agnostic. The parser collects all assertions from the script, identifies the `check-sat` command and its variant, and produces a single self-contained query — structurally identical to what a binary client would send.

### Response format

Text requests get text responses (standard SMT-LIB output: `sat`/`unsat`, `(model ...)`, etc.). Text response frames use the same transport framing: `u32_le frame_len` followed by the UTF-8 response bytes. Binary responses to text requests are deferred until a concrete text-request option is specified; the default is symmetric: text in, text out.

---

## 10. Server Internals

### Cache layer

The cache sits between the frontend decoders and the backend dispatch. Cache implementation is deferred until after response semantics are stable. A cache key must include every field that can affect the returned payload, including command, flags, expression buffer bytes, assertion roots, named assertion refs when cores can be returned, assumption roots, target node for optimization, and the cache policy for bounded timeouts. On cache hit, the response is returned immediately without invoking any solver. Cache entries are keyed per-format initially (binary and text queries cache independently). Cross-format dedup (hashing the parsed IR) is a future optimization that requires canonicalization.

### Backend translation

A single bottom-up pass over the node array, index 0 to N-1. For each node, build the corresponding backend term using already-translated children. The bottom-up construction order in the buffer guarantees children are always translated before parents.

Backend adapters are pluggable. A backend is eligible for a request only if it supports the requested command and response features: solving QF_BV + Bool, assumptions, timeout handling, model extraction for `WANT_MODEL`, unsat cores for `WANT_CORE`, simplification for `SIMPLIFY`, and optimization for `MINIMIZE`/`MAXIMIZE` as applicable. Phase 2 only requires Z3 support for `SOLVE`. Later phases can add binbit, Bitwuzla, or another backend behind the same adapter interface.

### Parallel dispatch

Both backends receive the translated formula simultaneously. The first to return wins. On `UNKNOWN` from one backend (timeout exhausted) the server waits for the other. On disagreement between backends (should not happen for correct implementations), log and flag for investigation.

### Solver pooling (optional optimization)

The server can maintain a pool of warm solver instances. When a new request arrives, it can be routed to a solver that already has structurally similar clauses loaded. This is invisible to the protocol — it's a performance optimization that doesn't affect correctness or the API contract.

---

## 11. Client Library Design

### Principles

- **Single file per language.** One header (C++), one `.py` file, one `.rs` file. No build system integration, no dependencies beyond the standard library.
- **No code generation.** The tag enum and node struct are hand-written. Adding a new operation is one enum variant and one builder function.
- **No networking.** The library produces and consumes byte buffers. The caller handles transport (`send`, `recv`, `write`, `read`). This keeps the library OS-agnostic and avoids pulling in socket, TLS, or async dependencies.
- **No allocator coupling.** C++ uses `std::vector` or a user-provided allocator. Rust uses `Vec`. Python uses `bytearray`. Override points are available but not required.

### Builder API surface

Every client library exposes the same logical API:

**Buffer management**: `new`, `reset`, `to_bytes` (serialize), `from_bytes` (zero-copy view).

**BV leaf constructors**: `bv_var(name, width) → NodeId`, `bv_const(value, width) → NodeId`, `bv_const_wide(limbs, width) → NodeId`.

**BV operations**: one function per tag — `bv_add(a, b)`, `bv_extract(x, hi, lo)`, `bv_ite(c, t, e)`, `bv_select(selectors, values, default)`, etc. Each returns a `NodeId`. Width is inferred from operands, validated, and stored in the node. `bv_select` must reject more than 127 selector/value pairs in v1 with a clear client-side error.

**Bool leaf constructors**: `bool_true()`, `bool_false()`, `bool_var(name)`.

**Bool operations**: `bool_not(a)`, `bool_and(a, b)`, `bool_or(a, b)`, `bool_implies(a, b)`.

**Comparisons and overflow**: `bv_eq(a, b)`, `bv_ult(a, b)`, `uadd_ovf(a, b)`, etc. Each returns a Bool `NodeId`.

**Convenience operations (lowered client-side)**: `bv_ne`, `bv_ugt`, `bv_uge`, `bv_sgt`, `bv_sge`, `bv_rotate_left`, `bv_rotate_right`, `assert_mutex`.

**Scope management**: `push()`, `pop()`, `assert(node)`, `assert_named(name, node)`, `assume(node)`.

**Request building**: `build_solve_request(budget_ms) → bytes`, `build_simplify_request(target) → bytes`, `build_minimize_request(target, signed, budget_ms) → bytes`.

**Response reading**: `parse_response(bytes) → Response` which exposes `status`, `model` (as an iterator of symbol→value pairs), `core` (as a list of assertion names), or `simplified_expr` (as a new buffer view).

### Hash-consing

Optional but strongly recommended. The builder maintains a map from `(tag, child0, child1, width)` to existing `NodeId`. DAG sharing is free — reusing a `NodeId` as a child of multiple parents is always safe.

### DAG compaction

Before serialization, the builder walks from assertion and assumption roots, marks reachable nodes, and emits only those into the wire buffer with renumbered IDs. This keeps the wire format tight after many push/pop cycles that leave dead nodes in the buffer.

---

## 12. BV_SELECT Encoding Detail

`BV_SELECT` is the one variadic node. Its children are interleaved selector/value pairs followed by the default:

```
children[0]     = selector_0 (Bool ref)
children[1]     = value_0    (BV ref)
children[2]     = selector_1 (Bool ref)
children[3]     = value_1    (BV ref)
...
children[2N-2]  = selector_{N-1}
children[2N-1]  = value_{N-1}
children[2N]    = default    (BV ref)
```

`arity = 2N + 1`. `aux_hi = N` (number of selector/value pairs). Because `arity` is a `u8`, v1 supports `0 <= N <= 127`; `N = 0` is a degenerate select that returns the default child. Validators must reject `BV_SELECT` nodes where `arity` is even or where `aux_hi != (arity - 1) / 2`. All values and default must have the same BV width. Selectors are Bool refs.

First-match semantics: the value associated with the earliest true selector is the result. If no selector is true, the default is used. Clients should pair `BV_SELECT` with pairwise mutual-exclusivity assertions on the selectors when applicable (emitted as normal assertions, not a special command).

---

## 13. Error Handling

### Client-side validation

The client libraries validate during construction: width mismatches, out-of-range extract bounds, sort mismatches in children (BV where Bool expected, etc.). Errors are reported immediately at the builder call site, not deferred to serialization or server response.

### Server-side validation

The server validates the request and expression buffer on decode. Malformed requests receive an `ERROR` response. The server must not crash or corrupt state on adversarial input.

Strict v1 validation rules:

- Frame length must match the binary request or response length implied by its header fields.
- Expression buffer length must equal `32 + node_count*24 + child_count*4 + blob_len`, computed with overflow-checked arithmetic.
- `node_count` must be `<= 2^31` so every node index is representable in a typed node ref.
- Expression buffer magic must be `"SMT\0"`, version must be `1`.
- All multi-byte fields are decoded little-endian using safe byte reads; implementations must not rely on host alignment.
- Reserved and tag-unused fields are ignored by validators. Encoders should write them as zero for deterministic hashes and tests.
- Tag values must be known v1 tags when solving or simplifying.
- `arity` must match the tag's required arity, except for `BV_SELECT` which uses `arity = 2N + 1`.
- `children + arity` must be within the child array when `arity > 0`.
- Every child/root/target/model node reference must have an index `< node_count` and a sort bit matching the referenced node's tag-derived sort.
- Every child reference must point to an earlier node index than the parent, enforcing bottom-up acyclic construction.
- Assertion roots and assumption roots must be Bool refs.
- `target_node` must be a BV or Bool ref for `SIMPLIFY`, a BV ref for `MINIMIZE`/`MAXIMIZE`, and zero for `SOLVE`.
- Bool-producing nodes must have `width = 0`; BV-producing nodes must have `width` in `1..65536`.
- BV binary operands must have equal widths; comparison and overflow operands must have equal widths.
- `BV_EXTRACT` must satisfy `0 <= aux_lo <= aux_hi < child_width`, and result width must be `aux_hi - aux_lo + 1`.
- `BV_CONCAT` result width must equal the sum of child widths and remain within the v1 width limit.
- `BV_ZEXT`/`BV_SEXT` result width must equal child width plus `aux_hi` and remain within the v1 width limit.
- Blob refs must be in bounds using overflow-checked `offset + len`. Symbol names must be valid UTF-8. Wide constants must reference exactly `ceil(width / 8)` bytes.
- `named_count <= assertion_count`; named assertion refs must point to valid UTF-8 names in the expression blob table.

### Budget exhaustion

A `SOLVE` or `MINIMIZE`/`MAXIMIZE` request with a nonzero millisecond `budget` may return `UNKNOWN` if the timeout is exhausted. This is not an error — it's an inconclusive result. The client decides whether to retry with a larger timeout, fall back to a different strategy, or treat the path as unknown.

---

## 14. Implementation Phases

The implementation should be staged so each phase has a testable artifact and works on Windows, macOS, and Linux.

### Phase 0 — Final v1 spec and golden vectors

- Keep this document as the v1 wire contract.
- Add golden byte-level tests for: empty expression buffer, simple SAT query, simple UNSAT query, wide constant, named assertion/core, malformed child index.
- Add conformance tests for little-endian decoding and response payload parsing.

### Phase 1 — Rust binary codec and builder

Rust is the preferred first implementation language because it gives safe cross-platform byte parsing, straightforward TCP support, and usable Z3 bindings. The server and reference client can share one Rust crate for constants, encoding, decoding, validation, and tests.

Deliverables:

- Tag/command/status/flag constants.
- Expression buffer parser/validator using safe unaligned reads.
- Expression builder with width/sort validation.
- Request/response envelope codecs.
- Response payload codecs for model/core/simplify/optimization blocks.
- Unit tests and fuzz-style malformed-input tests.

No solver backend is required in this phase.

### Phase 2 — SOLVE with one Z3 backend

- Translate validated IR to Z3 bottom-up.
- Implement `SOLVE` for SAT/UNSAT/UNKNOWN/ERROR.
- Implement model extraction for `WANT_MODEL`.
- Implement named assertions and unsat cores for `WANT_CORE`.
- Add a simple length-prefixed TCP server.
- Add CI for Windows, macOS, and Linux. Pin or document Z3 library provisioning for all three platforms.

This is the first useful end-to-end milestone.

### Phase 3 — Client libraries and compatibility polish

- Provide the Rust reference client as the canonical implementation.
- Add single-file C++ and Python builders once the Rust codec is stable.
- Add request-building helpers for push/pop, assumptions, compaction, and client-side lowerings.
- Add round-trip tests shared across languages using the golden vectors.

### Phase 4 — SMT-LIB text frontend

- Parse one complete length-prefixed SMT-LIB script per request.
- Reject unsupported incremental commands such as `push`/`pop`.
- Build the same internal IR as the binary frontend.
- Return standard text responses for text requests.

### Phase 5 — Second backend and backend racing

- Evaluate `binbit` (`https://github.com/bint-disasm/binbit`) as the preferred second backend if its API and cross-platform packaging fit the server.
- Use Bitwuzla as an alternative second backend if it is easier to package or exposes required features sooner.
- Add translation for the same validated IR to the chosen second backend.
- Race Z3 and the second backend for `SOLVE`.
- Log backend disagreements and preserve deterministic response semantics.

### Phase 6 — SIMPLIFY and optimization commands

- Implement `SIMPLIFY` response blocks.
- Implement `MINIMIZE`/`MAXIMIZE` with signed and unsigned ordering.
- Add optional model extraction for optimization commands.

### Phase 7 — Cache and server optimizations

- Add request/response caching after response semantics are stable.
- Include all fields that affect the returned payload in cache keys, including command, flags, expression bytes, roots, assumptions, target node, and timeout/cache policy.
- Add solver pooling and warm-start heuristics behind the same stateless protocol.

## 15. Future Considerations

Items explicitly deferred from v1 but anticipated in the design:

- **Delta compression**: for large base formulas, send only the diff from a previous request. Requires content-addressed node storage on the server. The expression buffer format is compatible — the header can gain a `base_hash` field referencing a previously cached buffer.
- **Array theory**: `QF_ABV` support. Would add `ARRAY_SELECT` and `ARRAY_STORE` tags plus a sort representation for arrays. The typed-reference scheme extends naturally (steal another bit or use a small sort table).
- **Streaming results**: for optimization queries (min/max), stream improving bounds as they're found rather than waiting for the optimal.
- **Cross-format cache dedup**: hash the canonicalized IR rather than the raw bytes to share cache entries between binary and text requests.
- **Additional backends**: binbit, Bitwuzla, Boolector, CVC5, or custom bitblasters. The backend interface is a single trait/interface (translate IR, solve, extract model).
- **Server-side warm-start**: route structurally similar queries to solvers with relevant learned clauses. Invisible to the protocol.
