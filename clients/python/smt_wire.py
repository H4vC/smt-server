"""Single-file Python builder/codec for the SMT v1 wire format.

The module intentionally has no dependencies beyond the standard library and
performs eager sort/width validation during construction.
"""
from __future__ import annotations

from dataclasses import dataclass
import socket
import struct
from typing import Iterable, Optional, Union

EXPR_MAGIC = b"SMT\0"
REQUEST_MAGIC = b"SMTQ"
RESPONSE_MAGIC = b"SMTR"
VERSION = 1
BOOL_BIT = 0x80000000
INDEX_MASK = 0x7fffffff
MAX_WIDTH = 65536

BV_VAR = 0
BV_CONST = 1
BV_NOT = 2
BV_NEG = 3
BV_AND = 4
BV_OR = 5
BV_XOR = 6
BV_ADD = 7
BV_SUB = 8
BV_MUL = 9
BV_UDIV = 10
BV_UREM = 11
BV_SDIV = 12
BV_SREM = 13
BV_SMOD = 14
BV_SHL = 15
BV_LSHR = 16
BV_ASHR = 17
BV_EXTRACT = 18
BV_CONCAT = 19
BV_ZEXT = 20
BV_SEXT = 21
BV_ITE = 22
BV_SELECT = 23
BOOL_TRUE = 24
BOOL_FALSE = 25
BOOL_VAR = 26
BOOL_NOT = 27
BOOL_AND = 28
BOOL_OR = 29
BOOL_IMPLIES = 30
BV_EQ = 31
BV_ULT = 32
BV_ULE = 33
BV_SLT = 34
BV_SLE = 35
UADD_OVF = 36
SADD_OVF = 37
USUB_OVF = 38
SSUB_OVF = 39
UMUL_OVF = 40
SMUL_OVF = 41
NEG_OVF = 42
SDIV_OVF = 43

SOLVE = 0
SIMPLIFY = 1
MINIMIZE = 2
MAXIMIZE = 3
WANT_MODEL = 1 << 0
WANT_CORE = 1 << 1
SIGNED = 1 << 2

OK = 0
SAT = 1
UNSAT = 2
UNKNOWN = 3
ERROR = 4
HAS_MODEL = 1 << 0
HAS_CORE = 1 << 1
HAS_EXPR = 1 << 2
HAS_VALUE = 1 << 3
HAS_MESSAGE = 1 << 4


def bv_ref(index: int) -> int:
    if not 0 <= index <= INDEX_MASK:
        raise ValueError("node index out of range")
    return index


def bool_ref(index: int) -> int:
    if not 0 <= index <= INDEX_MASK:
        raise ValueError("node index out of range")
    return BOOL_BIT | index


def ref_index(ref: int) -> int:
    return ref & INDEX_MASK


def is_bool_ref(ref: int) -> bool:
    return bool(ref & BOOL_BIT)


def is_bv_ref(ref: int) -> bool:
    return not is_bool_ref(ref)


def blob_payload(offset: int, length: int) -> int:
    return (offset << 32) | length


def bytes_for_width(width: int) -> int:
    if not 1 <= width <= MAX_WIDTH:
        raise ValueError(f"invalid BV width {width}")
    return (width + 7) // 8


@dataclass(frozen=True)
class Node:
    tag: int
    arity: int
    aux_hi: int
    width: int
    aux_lo: int
    children: int
    payload: int


@dataclass(frozen=True)
class ScalarValue:
    width: int
    bytes: bytes

    def as_bool(self) -> bool:
        if self.width != 0 or len(self.bytes) != 1:
            raise ValueError("scalar is not Bool")
        return self.bytes[0] != 0

    def as_int(self) -> int:
        return int.from_bytes(self.bytes, "little")


@dataclass(frozen=True)
class ModelEntry:
    node_ref: int
    value: ScalarValue


@dataclass(frozen=True)
class SimplifyResult:
    expression: bytes
    assertion_roots: list[int]
    named_assertion_refs: list[tuple[int, int]]
    assumption_roots: list[int]


@dataclass(frozen=True)
class OptimizationResult:
    optimum: ScalarValue
    model: Optional[list[ModelEntry]] = None


@dataclass(frozen=True)
class Response:
    request_id: int
    status: int
    flags: int
    payload: bytes

    def message(self) -> str:
        return self.payload.decode("utf-8")

    def model(self) -> list[ModelEntry]:
        return parse_model(self.payload)

    def core(self) -> list[str]:
        return parse_core(self.payload)

    def simplified(self) -> SimplifyResult:
        return parse_simplify(self.payload)

    def optimization(self) -> OptimizationResult:
        return parse_optimization(self.payload, bool(self.flags & HAS_MODEL))


class Builder:
    def __init__(self) -> None:
        self.nodes: list[Node] = []
        self.children: list[int] = []
        self.blob = bytearray()
        self.meta: list[tuple[str, int]] = []
        self.assertions: list[tuple[int, Optional[tuple[int, int]]]] = []
        self.assumptions: list[int] = []
        self.scopes: list[int] = []

    def reset(self) -> None:
        self.__init__()

    def push(self) -> None:
        self.scopes.append(len(self.assertions))

    def pop(self) -> None:
        if not self.scopes:
            raise ValueError("pop without push")
        del self.assertions[self.scopes.pop():]

    def _blob(self, data: bytes) -> tuple[int, int]:
        off = len(self.blob)
        self.blob.extend(data)
        return off, len(data)

    def _sort_for_tag(self, tag: int) -> str:
        return "bv" if tag <= BV_SELECT else "bool"

    def _push(self, tag: int, width: int, children: Iterable[int] = (), aux_hi: int = 0, aux_lo: int = 0, payload: int = 0) -> int:
        children = list(children)
        if len(children) > 255:
            raise ValueError("node arity exceeds u8")
        start = len(self.children) if children else 0
        for child in children:
            self._meta(child)
        self.children.extend(children)
        index = len(self.nodes)
        sort = self._sort_for_tag(tag)
        self.nodes.append(Node(tag, len(children), aux_hi, width, aux_lo, start, payload))
        self.meta.append((sort, width))
        return bool_ref(index) if sort == "bool" else bv_ref(index)

    def _meta(self, ref: int) -> tuple[str, int]:
        idx = ref_index(ref)
        if idx >= len(self.meta):
            raise ValueError("node reference out of range")
        sort, width = self.meta[idx]
        if (sort == "bool") != is_bool_ref(ref):
            raise ValueError("typed node reference sort mismatch")
        return sort, width

    def _expect_bv(self, ref: int) -> int:
        sort, width = self._meta(ref)
        if sort != "bv":
            raise ValueError("expected BV reference")
        return width

    def _expect_bool(self, ref: int) -> None:
        sort, _ = self._meta(ref)
        if sort != "bool":
            raise ValueError("expected Bool reference")

    def _same_bv(self, a: int, b: int) -> int:
        aw, bw = self._expect_bv(a), self._expect_bv(b)
        if aw != bw:
            raise ValueError("BV width mismatch")
        return aw

    def bv_var(self, name: str, width: int) -> int:
        if not 1 <= width <= MAX_WIDTH:
            raise ValueError("invalid BV width")
        return self._push(BV_VAR, width, payload=blob_payload(*self._blob(name.encode())))

    def bv_const(self, value: int, width: int) -> int:
        if not 1 <= width <= MAX_WIDTH:
            raise ValueError("invalid BV width")
        if width <= 64:
            payload = value & ((1 << width) - 1 if width < 64 else (1 << 64) - 1)
            return self._push(BV_CONST, width, payload=payload)
        masked = int(value) & ((1 << width) - 1)
        data = masked.to_bytes(bytes_for_width(width), "little", signed=False)
        return self.bv_const_wide(data, width)

    def bv_const_wide(self, data: bytes, width: int) -> int:
        if len(data) != bytes_for_width(width):
            raise ValueError("wide constant length does not match width")
        data = bytearray(data)
        valid = width % 8
        if valid:
            data[-1] &= (1 << valid) - 1
        if width <= 64:
            return self.bv_const(int.from_bytes(data, "little"), width)
        return self._push(BV_CONST, width, payload=blob_payload(*self._blob(bytes(data))))

    def _bv_unary(self, tag: int, x: int) -> int:
        return self._push(tag, self._expect_bv(x), [x])

    def _bv_binary(self, tag: int, a: int, b: int) -> int:
        return self._push(tag, self._same_bv(a, b), [a, b])

    def _bool_binary(self, tag: int, a: int, b: int) -> int:
        self._expect_bool(a); self._expect_bool(b)
        return self._push(tag, 0, [a, b])

    def _bv_cmp(self, tag: int, a: int, b: int) -> int:
        self._same_bv(a, b)
        return self._push(tag, 0, [a, b])

    def bv_not(self, x: int) -> int: return self._bv_unary(BV_NOT, x)
    def bv_neg(self, x: int) -> int: return self._bv_unary(BV_NEG, x)
    def bv_and(self, a: int, b: int) -> int: return self._bv_binary(BV_AND, a, b)
    def bv_or(self, a: int, b: int) -> int: return self._bv_binary(BV_OR, a, b)
    def bv_xor(self, a: int, b: int) -> int: return self._bv_binary(BV_XOR, a, b)
    def bv_add(self, a: int, b: int) -> int: return self._bv_binary(BV_ADD, a, b)
    def bv_sub(self, a: int, b: int) -> int: return self._bv_binary(BV_SUB, a, b)
    def bv_mul(self, a: int, b: int) -> int: return self._bv_binary(BV_MUL, a, b)
    def bv_udiv(self, a: int, b: int) -> int: return self._bv_binary(BV_UDIV, a, b)
    def bv_urem(self, a: int, b: int) -> int: return self._bv_binary(BV_UREM, a, b)
    def bv_sdiv(self, a: int, b: int) -> int: return self._bv_binary(BV_SDIV, a, b)
    def bv_srem(self, a: int, b: int) -> int: return self._bv_binary(BV_SREM, a, b)
    def bv_smod(self, a: int, b: int) -> int: return self._bv_binary(BV_SMOD, a, b)
    def bv_shl(self, a: int, b: int) -> int: return self._bv_binary(BV_SHL, a, b)
    def bv_lshr(self, a: int, b: int) -> int: return self._bv_binary(BV_LSHR, a, b)
    def bv_ashr(self, a: int, b: int) -> int: return self._bv_binary(BV_ASHR, a, b)

    def bv_extract(self, x: int, hi: int, lo: int) -> int:
        width = self._expect_bv(x)
        if not 0 <= lo <= hi < width or hi > 0xffff:
            raise ValueError("invalid extract bounds")
        return self._push(BV_EXTRACT, hi - lo + 1, [x], hi, lo)

    def bv_concat(self, high: int, low: int) -> int:
        width = self._expect_bv(high) + self._expect_bv(low)
        if width > MAX_WIDTH:
            raise ValueError("concat width exceeds limit")
        return self._push(BV_CONCAT, width, [high, low])

    def bv_zext(self, x: int, amount: int) -> int:
        return self._extend(BV_ZEXT, x, amount)

    def bv_sext(self, x: int, amount: int) -> int:
        return self._extend(BV_SEXT, x, amount)

    def _extend(self, tag: int, x: int, amount: int) -> int:
        width = self._expect_bv(x) + amount
        if not 0 <= amount <= 0xffff or width > MAX_WIDTH:
            raise ValueError("invalid extension amount")
        return self._push(tag, width, [x], amount)

    def bv_ite(self, cond: int, then_value: int, else_value: int) -> int:
        self._expect_bool(cond)
        return self._push(BV_ITE, self._same_bv(then_value, else_value), [cond, then_value, else_value])

    def bv_select(self, selectors: list[int], values: list[int], default: int) -> int:
        if len(selectors) != len(values) or len(selectors) > 127:
            raise ValueError("invalid BV_SELECT pair count")
        width = self._expect_bv(default)
        children: list[int] = []
        for s, v in zip(selectors, values):
            self._expect_bool(s)
            if self._expect_bv(v) != width:
                raise ValueError("BV_SELECT width mismatch")
            children += [s, v]
        children.append(default)
        return self._push(BV_SELECT, width, children, len(selectors))

    def bool_true(self) -> int: return self._push(BOOL_TRUE, 0)
    def bool_false(self) -> int: return self._push(BOOL_FALSE, 0)
    def bool_var(self, name: str) -> int: return self._push(BOOL_VAR, 0, payload=blob_payload(*self._blob(name.encode())))
    def bool_not(self, x: int) -> int:
        self._expect_bool(x)
        return self._push(BOOL_NOT, 0, [x])
    def bool_and(self, a: int, b: int) -> int: return self._bool_binary(BOOL_AND, a, b)
    def bool_or(self, a: int, b: int) -> int: return self._bool_binary(BOOL_OR, a, b)
    def bool_implies(self, a: int, b: int) -> int: return self._bool_binary(BOOL_IMPLIES, a, b)

    def bv_eq(self, a: int, b: int) -> int: return self._bv_cmp(BV_EQ, a, b)
    def bv_ult(self, a: int, b: int) -> int: return self._bv_cmp(BV_ULT, a, b)
    def bv_ule(self, a: int, b: int) -> int: return self._bv_cmp(BV_ULE, a, b)
    def bv_slt(self, a: int, b: int) -> int: return self._bv_cmp(BV_SLT, a, b)
    def bv_sle(self, a: int, b: int) -> int: return self._bv_cmp(BV_SLE, a, b)
    def uadd_ovf(self, a: int, b: int) -> int: return self._bv_cmp(UADD_OVF, a, b)
    def sadd_ovf(self, a: int, b: int) -> int: return self._bv_cmp(SADD_OVF, a, b)
    def usub_ovf(self, a: int, b: int) -> int: return self._bv_cmp(USUB_OVF, a, b)
    def ssub_ovf(self, a: int, b: int) -> int: return self._bv_cmp(SSUB_OVF, a, b)
    def umul_ovf(self, a: int, b: int) -> int: return self._bv_cmp(UMUL_OVF, a, b)
    def smul_ovf(self, a: int, b: int) -> int: return self._bv_cmp(SMUL_OVF, a, b)
    def neg_ovf(self, x: int) -> int:
        self._expect_bv(x)
        return self._push(NEG_OVF, 0, [x])
    def sdiv_ovf(self, a: int, b: int) -> int: return self._bv_cmp(SDIV_OVF, a, b)

    def bv_ne(self, a: int, b: int) -> int: return self.bool_not(self.bv_eq(a, b))
    def bv_ugt(self, a: int, b: int) -> int: return self.bv_ult(b, a)
    def bv_uge(self, a: int, b: int) -> int: return self.bv_ule(b, a)
    def bv_sgt(self, a: int, b: int) -> int: return self.bv_slt(b, a)
    def bv_sge(self, a: int, b: int) -> int: return self.bv_sle(b, a)

    def bool_eq(self, a: int, b: int) -> int:
        self._expect_bool(a); self._expect_bool(b)
        return self.bool_and(self.bool_or(a, self.bool_not(b)), self.bool_or(self.bool_not(a), b))

    def bool_xor(self, a: int, b: int) -> int: return self.bool_not(self.bool_eq(a, b))

    def bool_ite(self, c: int, t: int, e: int) -> int:
        return self.bool_or(self.bool_and(c, t), self.bool_and(self.bool_not(c), e))

    def bv_rotate_left(self, x: int, amount: int) -> int:
        width = self._expect_bv(x)
        amount %= width
        if amount == 0:
            return x
        return self.bv_or(self.bv_shl(x, self.bv_const(amount, width)), self.bv_lshr(x, self.bv_const(width - amount, width)))

    def bv_rotate_right(self, x: int, amount: int) -> int:
        width = self._expect_bv(x)
        amount %= width
        if amount == 0:
            return x
        return self.bv_or(self.bv_lshr(x, self.bv_const(amount, width)), self.bv_shl(x, self.bv_const(width - amount, width)))

    def assert_(self, root: int) -> None:
        self._expect_bool(root)
        self.assertions.append((root, None))

    def assert_named(self, name: str, root: int) -> None:
        self._expect_bool(root)
        self.assertions.append((root, self._blob(name.encode())))

    def assume(self, root: int) -> None:
        self._expect_bool(root)
        self.assumptions.append(root)

    def assert_mutex(self, selectors: list[int]) -> None:
        for s in selectors: self._expect_bool(s)
        for i in range(len(selectors)):
            for j in range(i + 1, len(selectors)):
                self.assert_(self.bool_not(self.bool_and(selectors[i], selectors[j])))

    def to_bytes(self) -> bytes:
        return self._expr_bytes(self.nodes, self.children, self.blob)

    def _expr_bytes(self, nodes: list[Node], children: list[int], blob: bytes | bytearray) -> bytes:
        out = bytearray(EXPR_MAGIC + bytes([VERSION, 0, 0, 0]) + struct.pack("<III", len(nodes), len(children), len(blob)) + bytes(12))
        for n in nodes:
            out.extend(struct.pack("<BBHIIIQ", n.tag, n.arity, n.aux_hi, n.width, n.aux_lo, n.children, n.payload))
        for c in children:
            out.extend(struct.pack("<I", c))
        out.extend(blob)
        return bytes(out)

    def _mark(self, ref: int, live: set[int]) -> None:
        idx = ref_index(ref)
        if idx in live:
            return
        live.add(idx)
        node = self.nodes[idx]
        for i in range(node.arity):
            self._mark(self.children[node.children + i], live)

    def _compact(self, roots: list[int]) -> tuple[bytes, dict[int, int]]:
        live: set[int] = set()
        for r in roots:
            self._mark(r, live)
        old_to_new: dict[int, int] = {}
        new_nodes: list[Node] = []
        new_children: list[int] = []
        for old, node in enumerate(self.nodes):
            if old in live:
                sort, _ = self.meta[old]
                old_to_new[old] = bool_ref(len(new_nodes)) if sort == "bool" else bv_ref(len(new_nodes))
                new_nodes.append(node)
        for old, node in enumerate(self.nodes):
            if old not in live:
                continue
            start = len(new_children) if node.arity else 0
            for i in range(node.arity):
                child = self.children[node.children + i]
                new_children.append(old_to_new[ref_index(child)])
            new_nodes[ref_index(old_to_new[old])] = Node(node.tag, node.arity, node.aux_hi, node.width, node.aux_lo, start, node.payload)
        return self._expr_bytes(new_nodes, new_children, self.blob), old_to_new

    def build_request(self, request_id: int, command: int, flags: int = 0, budget_ms: int = 0, target: Optional[int] = None) -> bytes:
        named = [(r, n) for r, n in self.assertions if n is not None]
        unnamed = [(r, n) for r, n in self.assertions if n is None]
        assertions = named + unnamed
        roots = [r for r, _ in assertions] + self.assumptions + ([target] if target is not None else [])
        expr, remap = self._compact(roots)
        assertion_roots = [remap[ref_index(r)] for r, _ in assertions]
        assumption_roots = [remap[ref_index(r)] for r in self.assumptions]
        target_raw = remap[ref_index(target)] if target is not None else 0
        out = bytearray(REQUEST_MAGIC + struct.pack("<I", request_id) + bytes([command, flags]) + struct.pack("<I", budget_ms) + struct.pack("<I", len(expr)) + struct.pack("<HHH", len(assertion_roots), len(named), len(assumption_roots)) + struct.pack("<I", target_raw) + bytes(4))
        out.extend(expr)
        for r in assertion_roots: out.extend(struct.pack("<I", r))
        for _, name in named:
            assert name is not None
            out.extend(struct.pack("<II", name[0], name[1]))
        for r in assumption_roots: out.extend(struct.pack("<I", r))
        return bytes(out)

    def build_solve_request(self, request_id: int, budget_ms: int = 0, want_model: bool = False, want_core: bool = False) -> bytes:
        flags = (WANT_MODEL if want_model else 0) | (WANT_CORE if want_core else 0)
        return self.build_request(request_id, SOLVE, flags, budget_ms)

    def build_simplify_request(self, request_id: int) -> bytes:
        return self.build_request(request_id, SIMPLIFY)

    def build_minimize_request(self, request_id: int, target: int, signed: bool = False, budget_ms: int = 0, want_model: bool = False) -> bytes:
        self._expect_bv(target)
        return self.build_request(request_id, MINIMIZE, (SIGNED if signed else 0) | (WANT_MODEL if want_model else 0), budget_ms, target)

    def build_maximize_request(self, request_id: int, target: int, signed: bool = False, budget_ms: int = 0, want_model: bool = False) -> bytes:
        self._expect_bv(target)
        return self.build_request(request_id, MAXIMIZE, (SIGNED if signed else 0) | (WANT_MODEL if want_model else 0), budget_ms, target)


def parse_response(data: bytes) -> Response:
    if len(data) < 16 or data[:4] != RESPONSE_MAGIC:
        raise ValueError("bad response envelope")
    request_id, = struct.unpack_from("<I", data, 4)
    status = data[8]
    flags = data[9]
    payload_len, = struct.unpack_from("<I", data, 10)
    if len(data) != 16 + payload_len:
        raise ValueError("response length mismatch")
    return Response(request_id, status, flags, data[16:])


def _need(data: bytes, offset: int, length: int, context: str) -> None:
    if offset + length > len(data):
        raise ValueError(f"short {context}")


def parse_scalar(data: bytes, offset: int = 0) -> tuple[ScalarValue, int]:
    _need(data, offset, 8, "scalar header")
    width, value_len = struct.unpack_from("<II", data, offset)
    offset += 8
    _need(data, offset, value_len, "scalar value")
    raw = bytes(data[offset:offset + value_len])
    offset += value_len
    if width == 0:
        if value_len != 1 or raw[0] not in (0, 1):
            raise ValueError("invalid Bool scalar")
    else:
        expected = bytes_for_width(width)
        if value_len != expected:
            raise ValueError("invalid BV scalar length")
        valid = width % 8
        if valid and raw and (raw[-1] & ~((1 << valid) - 1)):
            raise ValueError("unused high bits are set in BV scalar")
    return ScalarValue(width, raw), offset


def parse_model(payload: bytes) -> list[ModelEntry]:
    _need(payload, 0, 4, "model header")
    count, = struct.unpack_from("<I", payload, 0)
    offset = 4
    entries: list[ModelEntry] = []
    for _ in range(count):
        _need(payload, offset, 4, "model node_ref")
        node_ref, = struct.unpack_from("<I", payload, offset)
        offset += 4
        value, offset = parse_scalar(payload, offset)
        entries.append(ModelEntry(node_ref, value))
    if offset != len(payload):
        raise ValueError("trailing bytes in model block")
    return entries


def parse_core(payload: bytes) -> list[str]:
    _need(payload, 0, 4, "unsat core header")
    count, = struct.unpack_from("<I", payload, 0)
    offset = 4
    names: list[str] = []
    for _ in range(count):
        _need(payload, offset, 4, "unsat core name length")
        length, = struct.unpack_from("<I", payload, offset)
        offset += 4
        _need(payload, offset, length, "unsat core name")
        names.append(payload[offset:offset + length].decode("utf-8"))
        offset += length
    if offset != len(payload):
        raise ValueError("trailing bytes in unsat core block")
    return names


def parse_simplify(payload: bytes) -> SimplifyResult:
    _need(payload, 0, 12, "simplify header")
    expr_len, assertion_count, named_count, assumption_count, _reserved = struct.unpack_from("<IHHHH", payload, 0)
    if named_count > assertion_count:
        raise ValueError("named_count exceeds assertion_count")
    offset = 12
    _need(payload, offset, expr_len, "simplify expression")
    expression = bytes(payload[offset:offset + expr_len])
    offset += expr_len
    _need(payload, offset, assertion_count * 4, "simplify assertion roots")
    assertion_roots = list(struct.unpack_from(f"<{assertion_count}I", payload, offset)) if assertion_count else []
    offset += assertion_count * 4
    named_assertion_refs: list[tuple[int, int]] = []
    for _ in range(named_count):
        _need(payload, offset, 8, "simplify named ref")
        named_assertion_refs.append(struct.unpack_from("<II", payload, offset))
        offset += 8
    _need(payload, offset, assumption_count * 4, "simplify assumption roots")
    assumption_roots = list(struct.unpack_from(f"<{assumption_count}I", payload, offset)) if assumption_count else []
    offset += assumption_count * 4
    if offset != len(payload):
        raise ValueError("trailing bytes in simplify block")
    return SimplifyResult(expression, assertion_roots, named_assertion_refs, assumption_roots)


def parse_optimization(payload: bytes, has_model: bool = False) -> OptimizationResult:
    optimum, offset = parse_scalar(payload, 0)
    model = None
    if has_model:
        model = parse_model(payload[offset:])
        offset = len(payload)
    if offset != len(payload):
        raise ValueError("trailing bytes in optimization block")
    return OptimizationResult(optimum, model)


def frame(payload: bytes) -> bytes:
    return struct.pack("<I", len(payload)) + payload


def recv_exact(sock: socket.socket, length: int) -> bytes:
    chunks: list[bytes] = []
    remaining = length
    while remaining:
        chunk = sock.recv(remaining)
        if not chunk:
            raise EOFError("socket closed while reading frame")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


class TcpClient:
    """Blocking TCP client for the SMT server transport."""

    def __init__(
        self,
        host: str = "127.0.0.1",
        port: int = 9123,
        timeout: Optional[float] = None,
        sock: Optional[socket.socket] = None,
    ) -> None:
        self._sock = sock if sock is not None else socket.create_connection((host, port), timeout=timeout)

    @classmethod
    def from_socket(cls, sock: socket.socket) -> "TcpClient":
        return cls(sock=sock)

    def close(self) -> None:
        self._sock.close()

    def __enter__(self) -> "TcpClient":
        return self

    def __exit__(self, *exc_info: object) -> None:
        self.close()

    def send_payload(self, payload: bytes) -> bytes:
        self._sock.sendall(frame(payload))
        (length,) = struct.unpack("<I", recv_exact(self._sock, 4))
        return recv_exact(self._sock, length)

    def send_request(self, request: bytes) -> Response:
        return parse_response(self.send_payload(request))

    def send_text(self, script: Union[str, bytes]) -> str:
        payload = script.encode("utf-8") if isinstance(script, str) else script
        return self.send_payload(payload).decode("utf-8")
