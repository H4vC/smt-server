"""Typed Python client for the SMT v1 wire protocol.

The public API is intentionally context-oriented: users build formulas through
``Context`` and send them through ``Client``.  ``Term`` objects are thin typed
handles.  The binary wire format remains a flat DAG of fixed-size records; all
serialization details are kept private to this module.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, IntEnum, IntFlag
import itertools
import re
import socket
import struct
from typing import Any, Callable, Iterable, Iterator, Literal, Optional, TypeVar

EXPR_MAGIC = b"SMT\0"
REQUEST_MAGIC = b"SMTQ"
RESPONSE_MAGIC = b"SMTR"
VERSION = 1
BOOL_BIT = 0x80000000
INDEX_MASK = 0x7FFFFFFF
MAX_WIDTH = 65536
DEFAULT_MAX_RESPONSE_BYTES = 64 * 1024 * 1024


class SmtError(ValueError):
    """Base class for SMT client validation and protocol errors."""


class SortError(SmtError):
    """Raised when an operation receives a term with the wrong sort."""


class WidthMismatchError(SmtError):
    """Raised when a bit-vector operation receives incompatible widths."""


class ContextMismatchError(SmtError):
    """Raised when an operation mixes terms from different contexts."""


class ProtocolError(SmtError):
    """Raised when a received or constructed wire payload is invalid."""


class Sort(Enum):
    BV = "bv"
    BOOL = "bool"


class _NamedIntEnum(IntEnum):
    def __str__(self) -> str:
        return f"{type(self).__name__}.{self.name}"


class _NamedIntFlag(IntFlag):
    def __str__(self) -> str:
        name = self.name
        if name is not None:
            return f"{type(self).__name__}.{name}"
        return f"{type(self).__name__}({int(self)})"


def _op(value: int, symbol: str) -> Any:
    return (value, symbol)


class Op(_NamedIntEnum):
    """Binary node tag with an SMT-LIB symbol for visitors and printing."""

    symbol: str

    def __new__(cls, value: int, symbol: str = "") -> Op:
        obj = int.__new__(cls, value)
        obj._value_ = value
        obj.symbol = symbol
        return obj

    BV_VAR = _op(0, "var")
    BV_CONST = _op(1, "const")
    BV_NOT = _op(2, "bvnot")
    BV_NEG = _op(3, "bvneg")
    BV_AND = _op(4, "bvand")
    BV_OR = _op(5, "bvor")
    BV_XOR = _op(6, "bvxor")
    BV_ADD = _op(7, "bvadd")
    BV_SUB = _op(8, "bvsub")
    BV_MUL = _op(9, "bvmul")
    BV_UDIV = _op(10, "bvudiv")
    BV_UREM = _op(11, "bvurem")
    BV_SDIV = _op(12, "bvsdiv")
    BV_SREM = _op(13, "bvsrem")
    BV_SMOD = _op(14, "bvsmod")
    BV_SHL = _op(15, "bvshl")
    BV_LSHR = _op(16, "bvlshr")
    BV_ASHR = _op(17, "bvashr")
    BV_EXTRACT = _op(18, "extract")
    BV_CONCAT = _op(19, "concat")
    BV_ZEXT = _op(20, "zero_extend")
    BV_SEXT = _op(21, "sign_extend")
    BV_ITE = _op(22, "ite")
    BV_SELECT = _op(23, "select")
    BOOL_TRUE = _op(24, "true")
    BOOL_FALSE = _op(25, "false")
    BOOL_VAR = _op(26, "var")
    BOOL_NOT = _op(27, "not")
    BOOL_AND = _op(28, "and")
    BOOL_OR = _op(29, "or")
    BOOL_IMPLIES = _op(30, "=>")
    BV_EQ = _op(31, "=")
    BV_ULT = _op(32, "bvult")
    BV_ULE = _op(33, "bvule")
    BV_SLT = _op(34, "bvslt")
    BV_SLE = _op(35, "bvsle")
    UADD_OVF = _op(36, "bvuaddo")
    SADD_OVF = _op(37, "bvsaddo")
    USUB_OVF = _op(38, "bvusubo")
    SSUB_OVF = _op(39, "bvssubo")
    UMUL_OVF = _op(40, "bvumulo")
    SMUL_OVF = _op(41, "bvsmulo")
    NEG_OVF = _op(42, "bvnego")
    SDIV_OVF = _op(43, "bvsdivo")


del _op


class Command(_NamedIntEnum):
    SOLVE = 0
    SIMPLIFY = 1
    MINIMIZE = 2
    MAXIMIZE = 3


class RequestFlag(_NamedIntFlag):
    WANT_MODEL = 1 << 0
    WANT_CORE = 1 << 1
    SIGNED = 1 << 2


class Status(_NamedIntEnum):
    SIMPLIFIED = 0
    SAT = 1
    UNSAT = 2
    UNKNOWN = 3
    ERROR = 4


class ResponseFlag(_NamedIntFlag):
    HAS_MODEL = 1 << 0
    HAS_CORE = 1 << 1
    HAS_EXPR = 1 << 2
    HAS_VALUE = 1 << 3
    HAS_MESSAGE = 1 << 4

    @classmethod
    def all_bits(cls) -> int:
        return int(
            cls.HAS_MODEL
            | cls.HAS_CORE
            | cls.HAS_EXPR
            | cls.HAS_VALUE
            | cls.HAS_MESSAGE
        )


def _bv_ref(index: int) -> int:
    if not 0 <= index <= INDEX_MASK:
        raise ProtocolError("node index out of range")
    return index


def _bool_ref(index: int) -> int:
    if not 0 <= index <= INDEX_MASK:
        raise ProtocolError("node index out of range")
    return BOOL_BIT | index


def _ref_index(ref: int) -> int:
    return ref & INDEX_MASK


def _is_bool_ref(ref: int) -> bool:
    return bool(ref & BOOL_BIT)


def _blob_payload(offset: int, length: int) -> int:
    return (offset << 32) | length


def _blob_ref(payload: int) -> tuple[int, int]:
    return (payload >> 32, payload & 0xFFFFFFFF)


def _bytes_for_width(width: int) -> int:
    if not 1 <= width <= MAX_WIDTH:
        raise WidthMismatchError(f"invalid BV width {width}")
    return (width + 7) // 8


@dataclass(frozen=True)
class Node:
    tag: Op
    arity: int
    aux_hi: int
    width: int
    aux_lo: int
    children: int
    payload: int


@dataclass(frozen=True)
class NodeMeta:
    sort: Sort
    width: int


@dataclass(frozen=True)
class _Assertion:
    root: int
    name: Optional[tuple[int, int]] = None


@dataclass(frozen=True)
class ScalarValue:
    width: int
    bytes: bytes

    def as_bool(self) -> bool:
        if self.width != 0 or len(self.bytes) != 1:
            raise SmtError("scalar is not Bool")
        return self.bytes[0] != 0

    def as_int(self) -> int:
        if self.width == 0:
            return int(self.as_bool())
        return int.from_bytes(self.bytes, "little")

    def __int__(self) -> int:
        return self.as_int()

    def __index__(self) -> int:
        return self.as_int()

    def __repr__(self) -> str:
        if self.width == 0:
            return f"ScalarValue(Bool={self.as_bool()})"
        return f"ScalarValue(BV{self.width}=0x{self.as_int():x})"


@dataclass(frozen=True)
class _RawModelEntry:
    node_ref: int
    value: ScalarValue


@dataclass(frozen=True)
class _SimplifyBlock:
    expression: bytes
    target_node: int


@dataclass(frozen=True)
class _OptimizationBlock:
    optimum: ScalarValue
    model_entries: Optional[list[_RawModelEntry]] = None


@dataclass(frozen=True)
class _RawResponse:
    request_id: int
    status: Status
    flags: ResponseFlag
    payload: bytes

    def message(self) -> str:
        return self.payload.decode("utf-8")


@dataclass(frozen=True)
class _Request:
    payload: bytes
    command: Command
    context: Context
    old_to_new: dict[int, int]
    new_to_old: dict[int, int]
    target: Optional[Term] = None


_VisitResult = TypeVar("_VisitResult")


class Term:
    """Base class for typed SMT terms."""

    __slots__ = ("_ctx", "_ref")

    def __init__(self, ctx: Context, ref: int) -> None:
        self._ctx = ctx
        self._ref = ref

    @property
    def context(self) -> Context:
        return self._ctx

    @property
    def id(self) -> int:
        """Node index used in SMT-LIB debugging placeholders such as ``|#12|``."""
        return _ref_index(self._ref)

    @property
    def sort(self) -> Sort:
        return self._ctx._meta_for_ref(self._ref).sort

    @property
    def op(self) -> Op:
        """Stable operation kind for visitors and IR translation.

        The enum discriminants are exactly the binary node tags used on the
        wire, so ``int(term.op)`` is the protocol tag.
        """
        return self._ctx._node_for_ref(self._ref).tag

    @property
    def children(self) -> tuple[Term, ...]:
        node = self._ctx._node_for_ref(self._ref)
        return tuple(
            self._ctx._term(self._ctx._children[node.children + i])
            for i in range(node.arity)
        )

    @property
    def name(self) -> str:
        """Variable name for ``Op.BV_VAR`` and ``Op.BOOL_VAR`` terms."""
        node = self._ctx._node_for_ref(self._ref)
        if node.tag not in (Op.BV_VAR, Op.BOOL_VAR):
            raise SmtError(f"term #{self.id} is not a variable")
        return self._ctx._blob_bytes(node.payload).decode("utf-8")

    @property
    def value(self) -> int:
        """Integer value for ``Op.BV_CONST`` terms."""
        node = self._ctx._node_for_ref(self._ref)
        if node.tag != Op.BV_CONST:
            raise SmtError(f"term #{self.id} is not a BV constant")
        return self._ctx._bv_const_value(node)

    @property
    def bool_value(self) -> bool:
        """Boolean value for ``Op.BOOL_TRUE`` and ``Op.BOOL_FALSE`` terms."""
        node = self._ctx._node_for_ref(self._ref)
        if node.tag == Op.BOOL_TRUE:
            return True
        if node.tag == Op.BOOL_FALSE:
            return False
        raise SmtError(f"term #{self.id} is not a Bool constant")

    @property
    def params(self) -> tuple[int, ...]:
        """Operation parameters not represented as child terms.

        Examples: ``Op.BV_EXTRACT`` returns ``(hi, lo)``, extensions return
        ``(amount,)``, and ``Op.BV_SELECT`` returns ``(pair_count,)``.
        """
        node = self._ctx._node_for_ref(self._ref)
        if node.tag == Op.BV_EXTRACT:
            return (node.aux_hi, node.aux_lo)
        if node.tag in (Op.BV_ZEXT, Op.BV_SEXT):
            return (node.aux_hi,)
        if node.tag == Op.BV_SELECT:
            return (node.aux_hi,)
        return ()

    def walk(
        self, order: Literal["pre", "post"] = "post", unique: bool = True
    ) -> Iterator[Term]:
        """Yield terms in preorder or postorder.

        ``unique=True`` preserves DAG sharing by yielding each node id at most
        once.  Use ``unique=False`` if the consumer wants tree-shaped traversal.
        """
        if order not in ("pre", "post"):
            raise ValueError("order must be 'pre' or 'post'")
        seen: set[int] = set()

        def go(term: Term) -> Iterator[Term]:
            if unique and term.id in seen:
                return
            if unique:
                seen.add(term.id)
            if order == "pre":
                yield term
            for child in term.children:
                yield from go(child)
            if order == "post":
                yield term

        yield from go(self)

    def visit(
        self, fn: Callable[[Term, tuple[_VisitResult, ...]], _VisitResult]
    ) -> _VisitResult:
        """Translate a term DAG with a memoized postorder visitor.

        ``fn`` is called once per reachable node with the term and the already
        translated child results.  The return value for the root is returned.
        """
        memo: dict[int, _VisitResult] = {}

        def go(term: Term) -> _VisitResult:
            if term.id in memo:
                return memo[term.id]
            result = fn(term, tuple(go(child) for child in term.children))
            memo[term.id] = result
            return result

        return go(self)

    def to_smt2(self, depth: int = -1) -> str:
        """Render this term as a depth-limited SMT-LIB expression.

        ``depth=0`` prints the root operation and abbreviates non-atomic child
        subtrees as quoted placeholder symbols like ``|#42|``.  ``depth=-1``
        disables the limit and expands the full DAG.  The root node id is
        appended as a trailing comment: ``; #id``.
        """
        return self._ctx._term_to_smt2(self, depth)

    def __str__(self) -> str:
        return self.to_smt2(depth=0)

    def __repr__(self) -> str:
        meta = self._ctx._meta_for_ref(self._ref)
        if meta.sort is Sort.BV:
            return f"BVTerm({self._ctx}#{self.id}: BV{meta.width})"
        return f"BoolTerm({self._ctx}#{self.id})"

    def __eq__(self, other: object) -> bool:
        """Python handle equality. Use Context.bv_eq/bool_eq for SMT equality."""
        return (
            isinstance(other, Term)
            and self._ctx is other._ctx
            and self._ref == other._ref
        )

    def __hash__(self) -> int:
        return hash((id(self._ctx), self._ref))

    def __bool__(self) -> bool:
        raise TypeError("SMT terms cannot be used as Python booleans")


class BVTerm(Term):
    """Thin bit-vector term handle. Dunders forward to the owning context."""

    @property
    def width(self) -> int:
        return self._ctx._expect_bv(self, "width")

    def __invert__(self) -> BVTerm:
        return self._ctx.bv_not(self)

    def __neg__(self) -> BVTerm:
        return self._ctx.bv_neg(self)

    def __and__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_and(self, other)

    def __rand__(self, other: int) -> BVTerm:
        return self._ctx.bv_and(self, other)

    def __or__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_or(self, other)

    def __ror__(self, other: int) -> BVTerm:
        return self._ctx.bv_or(self, other)

    def __xor__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_xor(self, other)

    def __rxor__(self, other: int) -> BVTerm:
        return self._ctx.bv_xor(self, other)

    def __add__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_add(self, other)

    def __radd__(self, other: int) -> BVTerm:
        return self._ctx.bv_add(self, other)

    def __sub__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_sub(self, other)

    def __rsub__(self, other: int) -> BVTerm:
        return self._ctx._bv_binary_reverse(Op.BV_SUB, self, other)

    def __mul__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_mul(self, other)

    def __rmul__(self, other: int) -> BVTerm:
        return self._ctx.bv_mul(self, other)

    def __lshift__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_shl(self, other)

    def __rlshift__(self, other: int) -> BVTerm:
        return self._ctx._bv_binary_reverse(Op.BV_SHL, self, other)

    def __rshift__(self, other: BVTerm | int) -> BVTerm:
        return self._ctx.bv_lshr(self, other)

    def __rrshift__(self, other: int) -> BVTerm:
        return self._ctx._bv_binary_reverse(Op.BV_LSHR, self, other)


class BoolTerm(Term):
    """Thin Boolean term handle. Dunders forward to the owning context."""

    def __invert__(self) -> BoolTerm:
        return self._ctx.bool_not(self)

    def __and__(self, other: BoolTerm) -> BoolTerm:
        return self._ctx.bool_and(self, other)

    def __or__(self, other: BoolTerm) -> BoolTerm:
        return self._ctx.bool_or(self, other)

    def __rshift__(self, other: BoolTerm) -> BoolTerm:
        return self._ctx.bool_implies(self, other)


_SIMPLE_SYMBOL = re.compile(
    r"^[A-Za-z_~!@$%^&*+=<>.?/\-][A-Za-z0-9_~!@$%^&*+=<>.?/\-]*$"
)
_RESERVED_SYMBOLS = {
    "let",
    "par",
    "forall",
    "exists",
    "match",
    "_",
    "!",
    "as",
    "true",
    "false",
}
_ATOM_OPS = frozenset(
    {Op.BV_VAR, Op.BV_CONST, Op.BOOL_TRUE, Op.BOOL_FALSE, Op.BOOL_VAR}
)


class Context:
    """Append-only SMT expression context that owns all term operations."""

    # Process-local debug ids only; they are not serialized or protocol-visible.
    _next_id = itertools.count(1)

    def __init__(self) -> None:
        self._id = next(Context._next_id)
        self._nodes: list[Node] = []
        self._children: list[int] = []
        self._blob = bytearray()
        self._assertions: list[_Assertion] = []
        self._assumptions: list[int] = []
        self._scopes: list[int] = []
        self._bv_vars: dict[tuple[str, int], int] = {}
        self._bool_vars: dict[str, int] = {}
        self._symbols: dict[str, NodeMeta] = {}
        self._term_cache: dict[int, Term] = {}

    @property
    def id(self) -> int:
        return self._id

    @property
    def node_count(self) -> int:
        return len(self._nodes)

    @property
    def assertion_count(self) -> int:
        return len(self._assertions)

    @property
    def assertions(self) -> list[BoolTerm]:
        """Current asserted terms, named and unnamed, as a new list."""
        return [self._bool_term(assertion.root) for assertion in self._assertions]

    @property
    def named_assertions(self) -> list[tuple[str, BoolTerm]]:
        """Current named assertions as ``(name, term)`` pairs in insertion order."""
        out: list[tuple[str, BoolTerm]] = []
        for assertion in self._assertions:
            if assertion.name is None:
                continue
            name = self._blob_bytes(_blob_payload(*assertion.name)).decode("utf-8")
            out.append((name, self._bool_term(assertion.root)))
        return out

    @property
    def assumptions(self) -> list[BoolTerm]:
        """Current assumptions as a new list. Assumptions are not scoped."""
        return [self._bool_term(root) for root in self._assumptions]

    def __str__(self) -> str:
        return f"Context#{self._id}"

    def __repr__(self) -> str:
        return f"Context#{self._id}(nodes={len(self._nodes)}, assertions={len(self._assertions)})"

    def to_smt2(self, *, check_sat: bool = True, get_model: bool = True) -> str:
        """Render this context as a self-contained SMT-LIB script.

        Current assumptions are emitted as assertions.  ``get_model=True`` also
        emits ``(set-option :produce-models true)`` and implies ``check_sat``.
        """
        if get_model:
            check_sat = True
        lines = ["(set-logic QF_BV)"]
        if get_model:
            lines.append("(set-option :produce-models true)")

        declarations: dict[str, NodeMeta] = {}
        for node in self._nodes:
            if node.tag == Op.BV_VAR:
                name = self._blob_bytes(node.payload).decode("utf-8")
                meta = NodeMeta(Sort.BV, node.width)
            elif node.tag == Op.BOOL_VAR:
                name = self._blob_bytes(node.payload).decode("utf-8")
                meta = NodeMeta(Sort.BOOL, 0)
            else:
                continue
            existing = declarations.get(name)
            if existing is None:
                declarations[name] = meta
            elif existing != meta:
                raise SortError(f"symbol {name!r} has multiple sorts in {self}")

        for name, meta in declarations.items():
            symbol = self._quote_symbol(name)
            if meta.sort is Sort.BV:
                lines.append(f"(declare-const {symbol} (_ BitVec {meta.width}))")
            else:
                lines.append(f"(declare-const {symbol} Bool)")

        for assertion in self._assertions:
            expr = self._render_smt2(assertion.root, None)
            if assertion.name is None:
                lines.append(f"(assert {expr}) ; #{_ref_index(assertion.root)}")
            else:
                name = self._quote_symbol(
                    self._blob_bytes(_blob_payload(*assertion.name)).decode("utf-8")
                )
                lines.append(
                    f"(assert (! {expr} :named {name})) ; #{_ref_index(assertion.root)}"
                )

        for root in self._assumptions:
            expr = self._render_smt2(root, None)
            lines.append(f"(assert {expr}) ; assumption #{_ref_index(root)}")

        if check_sat:
            lines.append("(check-sat)")
        if get_model:
            lines.append("(get-model)")
        return "\n".join(lines) + "\n"

    def bv_var(self, name: str, width: int) -> BVTerm:
        self._check_bv_width(width)
        self._check_symbol(name, NodeMeta(Sort.BV, width))
        key = (name, width)
        if key in self._bv_vars:
            return self._bv_term(self._bv_vars[key])
        ref = self._push_raw(
            Op.BV_VAR, width, payload=_blob_payload(*self._blob_ref_for(name.encode()))
        )
        self._bv_vars[key] = ref
        return self._bv_term(ref)

    def bool_var(self, name: str) -> BoolTerm:
        self._check_symbol(name, NodeMeta(Sort.BOOL, 0))
        if name in self._bool_vars:
            return self._bool_term(self._bool_vars[name])
        ref = self._push_raw(
            Op.BOOL_VAR, 0, payload=_blob_payload(*self._blob_ref_for(name.encode()))
        )
        self._bool_vars[name] = ref
        return self._bool_term(ref)

    def bv_const(self, value: int, width: int) -> BVTerm:
        self._check_bv_width(width)
        if width <= 64:
            mask = (1 << width) - 1 if width < 64 else (1 << 64) - 1
            return self._bv_term(
                self._push_raw(Op.BV_CONST, width, payload=int(value) & mask)
            )
        masked = int(value) & ((1 << width) - 1)
        data = masked.to_bytes(_bytes_for_width(width), "little", signed=False)
        return self.bv_const_wide(data, width)

    def bv_const_wide(self, data: bytes, width: int) -> BVTerm:
        self._check_bv_width(width)
        if len(data) != _bytes_for_width(width):
            raise WidthMismatchError("wide constant length does not match width")
        normalized = bytearray(data)
        valid = width % 8
        if valid:
            normalized[-1] &= (1 << valid) - 1
        if width <= 64:
            return self.bv_const(int.from_bytes(normalized, "little"), width)
        return self._bv_term(
            self._push_raw(
                Op.BV_CONST,
                width,
                payload=_blob_payload(*self._blob_ref_for(bytes(normalized))),
            )
        )

    def bool_const(self, value: bool) -> BoolTerm:
        return self.true() if value else self.false()

    def true(self) -> BoolTerm:
        return self._bool_term(self._push_raw(Op.BOOL_TRUE, 0))

    def false(self) -> BoolTerm:
        return self._bool_term(self._push_raw(Op.BOOL_FALSE, 0))

    def bv_not(self, x: BVTerm) -> BVTerm:
        return self._bv_unary(Op.BV_NOT, x)

    def bv_neg(self, x: BVTerm) -> BVTerm:
        return self._bv_unary(Op.BV_NEG, x)

    def bv_and(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_AND, a, b)

    def bv_or(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_OR, a, b)

    def bv_xor(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_XOR, a, b)

    def bv_add(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_ADD, a, b)

    def bv_sub(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_SUB, a, b)

    def bv_mul(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_MUL, a, b)

    def bv_udiv(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_UDIV, a, b)

    def bv_urem(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_UREM, a, b)

    def bv_sdiv(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_SDIV, a, b)

    def bv_srem(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_SREM, a, b)

    def bv_smod(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_SMOD, a, b)

    def bv_shl(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_SHL, a, b)

    def bv_lshr(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_LSHR, a, b)

    def bv_ashr(self, a: BVTerm, b: BVTerm | int) -> BVTerm:
        return self._bv_binary(Op.BV_ASHR, a, b)

    def bv_eq(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.BV_EQ, a, b)

    def bv_ne(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self.bool_not(self.bv_eq(a, b))

    def bv_ult(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.BV_ULT, a, b)

    def bv_ule(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.BV_ULE, a, b)

    def bv_ugt(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp_reverse(Op.BV_ULT, a, b)

    def bv_uge(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp_reverse(Op.BV_ULE, a, b)

    def bv_slt(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.BV_SLT, a, b)

    def bv_sle(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.BV_SLE, a, b)

    def bv_sgt(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp_reverse(Op.BV_SLT, a, b)

    def bv_sge(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp_reverse(Op.BV_SLE, a, b)

    def bv_uadd_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.UADD_OVF, a, b)

    def bv_sadd_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.SADD_OVF, a, b)

    def bv_usub_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.USUB_OVF, a, b)

    def bv_ssub_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.SSUB_OVF, a, b)

    def bv_umul_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.UMUL_OVF, a, b)

    def bv_smul_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.SMUL_OVF, a, b)

    def bv_neg_overflows(self, x: BVTerm) -> BoolTerm:
        self._expect_bv(x, Op.NEG_OVF.symbol)
        return self._bool_term(self._push_raw(Op.NEG_OVF, 0, [x._ref]))

    def bv_sdiv_overflows(self, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        return self._bv_cmp(Op.SDIV_OVF, a, b)

    def bv_extract(self, x: BVTerm, hi: int, lo: int) -> BVTerm:
        width = self._expect_bv(x, "extract")
        if not 0 <= lo <= hi < width or hi > 0xFFFF:
            raise WidthMismatchError(
                f"extract: invalid bounds hi={hi}, lo={lo} for BV{width}"
            )
        return self._bv_term(
            self._push_raw(Op.BV_EXTRACT, hi - lo + 1, [x._ref], hi, lo)
        )

    def bv_concat(self, high: BVTerm, low: BVTerm) -> BVTerm:
        high_width = self._expect_bv(high, "concat")
        low_width = self._expect_bv(low, "concat")
        width = high_width + low_width
        self._check_bv_width(width, context="concat result")
        return self._bv_term(self._push_raw(Op.BV_CONCAT, width, [high._ref, low._ref]))

    def bv_zext(self, x: BVTerm, amount: int) -> BVTerm:
        return self._extend(Op.BV_ZEXT, x, amount)

    def bv_sext(self, x: BVTerm, amount: int) -> BVTerm:
        return self._extend(Op.BV_SEXT, x, amount)

    def bool_not(self, x: BoolTerm) -> BoolTerm:
        return self._bool_unary(Op.BOOL_NOT, x)

    def bool_and(self, a: BoolTerm, b: BoolTerm) -> BoolTerm:
        return self._bool_binary(Op.BOOL_AND, a, b)

    def bool_or(self, a: BoolTerm, b: BoolTerm) -> BoolTerm:
        return self._bool_binary(Op.BOOL_OR, a, b)

    def bool_implies(self, a: BoolTerm, b: BoolTerm) -> BoolTerm:
        return self._bool_binary(Op.BOOL_IMPLIES, a, b)

    def bool_eq(self, a: BoolTerm, b: BoolTerm) -> BoolTerm:
        """Boolean equality, lowered client-side because the wire has no BOOL_EQ."""
        self._expect_bool(a, "=")
        if not isinstance(b, BoolTerm):
            raise SortError(f"=: expected Bool term, got {type(b).__name__}")
        self._expect_bool(b, "=")
        return self.bool_or(
            self.bool_and(a, b),
            self.bool_and(self.bool_not(a), self.bool_not(b)),
        )

    def ite(self, cond: BoolTerm, then_term: Term, else_term: Term) -> Term:
        """If-then-else. Bool branches lower because the wire has no BOOL_ITE."""
        self._expect_bool(cond, "ite")
        then_term = self._expect_term(then_term, "ite")
        else_term = self._expect_term(else_term, "ite")
        if then_term.sort is not else_term.sort:
            raise SortError(
                f"ite: branch sort mismatch ({then_term.sort.value} vs {else_term.sort.value})"
            )
        if isinstance(then_term, BVTerm):
            width = self._same_bv(then_term, else_term, "ite")
            return self._bv_term(
                self._push_raw(
                    Op.BV_ITE, width, [cond._ref, then_term._ref, else_term._ref]
                )
            )
        if not isinstance(then_term, BoolTerm) or not isinstance(else_term, BoolTerm):
            raise SortError("ite: expected both branches to be BV terms or Bool terms")
        self._expect_bool(then_term, "ite")
        self._expect_bool(else_term, "ite")
        return self.bool_or(
            self.bool_and(cond, then_term),
            self.bool_and(self.bool_not(cond), else_term),
        )

    def bv_select(
        self, selectors: list[BoolTerm], values: list[BVTerm], default: BVTerm
    ) -> BVTerm:
        if len(selectors) != len(values) or len(selectors) > 127:
            raise SmtError("select: selector/value count mismatch or count exceeds 127")
        width = self._expect_bv(default, "select")
        children: list[int] = []
        for selector, value in zip(selectors, values):
            self._expect_bool(selector, "select")
            if self._expect_bv(value, "select") != width:
                raise WidthMismatchError("select: value width mismatch")
            children.extend([selector._ref, value._ref])
        children.append(default._ref)
        return self._bv_term(
            self._push_raw(Op.BV_SELECT, width, children, len(selectors))
        )

    def bv_rotate_left(self, x: BVTerm, amount: int) -> BVTerm:
        """Rotate left by lowering to shifts and ORs; there is no rotate wire op."""
        width = self._expect_bv(x, "rotate_left")
        amount %= width
        if amount == 0:
            return x
        return self.bv_or(
            self.bv_shl(x, self.bv_const(amount, width)),
            self.bv_lshr(x, self.bv_const(width - amount, width)),
        )

    def bv_rotate_right(self, x: BVTerm, amount: int) -> BVTerm:
        """Rotate right by lowering to shifts and ORs; there is no rotate wire op."""
        width = self._expect_bv(x, "rotate_right")
        amount %= width
        if amount == 0:
            return x
        return self.bv_or(
            self.bv_lshr(x, self.bv_const(amount, width)),
            self.bv_shl(x, self.bv_const(width - amount, width)),
        )

    def assert_(self, root: BoolTerm) -> None:
        self._expect_bool(root, "assert")
        self._assertions.append(_Assertion(root._ref, None))

    def assert_named(self, name: str, root: BoolTerm) -> None:
        self._expect_bool(root, "assert_named")
        self._assertions.append(
            _Assertion(root._ref, self._blob_ref_for(name.encode()))
        )

    def assume(self, root: BoolTerm) -> None:
        """Add an assumption. Assumptions are not affected by push/pop."""
        self._expect_bool(root, "assume")
        self._assumptions.append(root._ref)

    def clear_assumptions(self) -> None:
        """Remove all current assumptions."""
        self._assumptions.clear()

    def push(self) -> None:
        """Save the assertion stack depth. Assumptions are not scoped."""
        self._scopes.append(len(self._assertions))

    def pop(self) -> None:
        """Restore assertions to the most recent push depth."""
        if not self._scopes:
            raise SmtError("pop without push")
        del self._assertions[self._scopes.pop() :]

    def assert_mutex(self, selectors: list[BoolTerm]) -> None:
        """Assert pairwise mutual exclusion; emits O(n²) assertions/nodes."""
        for selector in selectors:
            self._expect_bool(selector, "assert_mutex")
        for i in range(len(selectors)):
            for j in range(i + 1, len(selectors)):
                self.assert_(self.bool_not(self.bool_and(selectors[i], selectors[j])))

    def _check_bv_width(self, width: int, context: str = "BV width") -> None:
        if not 1 <= width <= MAX_WIDTH:
            raise WidthMismatchError(f"{context}: invalid width {width}")

    def _check_symbol(self, name: str, signature: NodeMeta) -> None:
        existing = self._symbols.get(name)
        if existing is None:
            self._symbols[name] = signature
        elif existing != signature:
            raise SortError(
                f"symbol {name!r} already has sort {existing.sort.value}"
                f"{existing.width if existing.sort is Sort.BV else ''}, cannot reuse as "
                f"{signature.sort.value}{signature.width if signature.sort is Sort.BV else ''}"
            )

    def _blob_ref_for(self, data: bytes) -> tuple[int, int]:
        offset = len(self._blob)
        self._blob.extend(data)
        return offset, len(data)

    def _tag_sort(self, tag: Op) -> Sort:
        return Sort.BV if tag <= Op.BV_SELECT else Sort.BOOL

    def _push_raw(
        self,
        tag: Op,
        width: int,
        children: Iterable[int] = (),
        aux_hi: int = 0,
        aux_lo: int = 0,
        payload: int = 0,
    ) -> int:
        child_list = list(children)
        if len(child_list) > 255:
            raise ProtocolError("node arity exceeds u8")
        start = len(self._children) if child_list else 0
        for child in child_list:
            self._meta_for_ref(child)
        self._children.extend(child_list)
        index = len(self._nodes)
        sort = self._tag_sort(tag)
        self._nodes.append(
            Node(tag, len(child_list), aux_hi, width, aux_lo, start, payload)
        )
        return _bool_ref(index) if sort is Sort.BOOL else _bv_ref(index)

    def _term(self, ref: int) -> Term:
        meta = self._meta_for_ref(ref)
        cached = self._term_cache.get(ref)
        if cached is not None:
            return cached
        term: Term = (
            BoolTerm(self, ref) if meta.sort is Sort.BOOL else BVTerm(self, ref)
        )
        self._term_cache[ref] = term
        return term

    def _bv_term(self, ref: int) -> BVTerm:
        term = self._term(ref)
        if not isinstance(term, BVTerm):
            raise SortError(f"internal error: expected BV term for reference {ref:#x}")
        return term

    def _bool_term(self, ref: int) -> BoolTerm:
        term = self._term(ref)
        if not isinstance(term, BoolTerm):
            raise SortError(
                f"internal error: expected Bool term for reference {ref:#x}"
            )
        return term

    def _meta_for_ref(self, ref: int) -> NodeMeta:
        idx = _ref_index(ref)
        if idx >= len(self._nodes):
            raise ProtocolError(f"node reference #{idx} out of range in {self}")
        node = self._nodes[idx]
        meta = NodeMeta(self._tag_sort(node.tag), node.width)
        if (meta.sort is Sort.BOOL) != _is_bool_ref(ref):
            raise SortError(f"typed node reference sort mismatch for #{idx}")
        return meta

    def _node_for_ref(self, ref: int) -> Node:
        self._meta_for_ref(ref)
        return self._nodes[_ref_index(ref)]

    def _expect_term(self, term: Term, op: str) -> Term:
        if not isinstance(term, Term):
            raise SortError(f"{op}: expected Term, got {type(term).__name__}")
        if term._ctx is not self:
            raise ContextMismatchError(f"{op}: term from {term._ctx}, expected {self}")
        self._meta_for_ref(term._ref)
        return term

    def _expect_bv(self, term: Term, op: str) -> int:
        term = self._expect_term(term, op)
        meta = self._meta_for_ref(term._ref)
        if meta.sort is not Sort.BV:
            raise SortError(
                f"{op}: expected BV term, got Bool term #{term.id} from {self}"
            )
        return meta.width

    def _expect_bool(self, term: Term, op: str) -> None:
        term = self._expect_term(term, op)
        meta = self._meta_for_ref(term._ref)
        if meta.sort is not Sort.BOOL:
            raise SortError(
                f"{op}: expected Bool term, got BV{meta.width} term #{term.id} from {self}"
            )

    def _coerce_bv_operand(self, value: BVTerm | int, width: int, op: str) -> BVTerm:
        if isinstance(value, bool):
            raise SortError(f"{op}: Python bool is not a bit-vector constant")
        if isinstance(value, int):
            return self.bv_const(value, width)
        if not isinstance(value, BVTerm):
            raise SortError(
                f"{op}: expected BV term or int, got {type(value).__name__}"
            )
        actual = self._expect_bv(value, op)
        if actual != width:
            raise WidthMismatchError(f"{op}: BV width mismatch ({width} vs {actual})")
        return value

    def _same_bv(self, a: Term, b: Term, op: str) -> int:
        aw = self._expect_bv(a, op)
        bw = self._expect_bv(b, op)
        if aw != bw:
            raise WidthMismatchError(f"{op}: BV width mismatch ({aw} vs {bw})")
        return aw

    def _bv_unary(self, tag: Op, x: BVTerm) -> BVTerm:
        width = self._expect_bv(x, tag.symbol)
        return self._bv_term(self._push_raw(tag, width, [x._ref]))

    def _bv_binary(self, tag: Op, a: BVTerm, b: BVTerm | int) -> BVTerm:
        width = self._expect_bv(a, tag.symbol)
        b = self._coerce_bv_operand(b, width, tag.symbol)
        return self._bv_term(self._push_raw(tag, width, [a._ref, b._ref]))

    def _bv_binary_reverse(self, tag: Op, a: BVTerm, b: BVTerm | int) -> BVTerm:
        width = self._expect_bv(a, tag.symbol)
        b = self._coerce_bv_operand(b, width, tag.symbol)
        return self._bv_term(self._push_raw(tag, width, [b._ref, a._ref]))

    def _bv_cmp(self, tag: Op, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        width = self._expect_bv(a, tag.symbol)
        b = self._coerce_bv_operand(b, width, tag.symbol)
        return self._bool_term(self._push_raw(tag, 0, [a._ref, b._ref]))

    def _bv_cmp_reverse(self, tag: Op, a: BVTerm, b: BVTerm | int) -> BoolTerm:
        width = self._expect_bv(a, tag.symbol)
        b = self._coerce_bv_operand(b, width, tag.symbol)
        return self._bool_term(self._push_raw(tag, 0, [b._ref, a._ref]))

    def _bool_unary(self, tag: Op, x: BoolTerm) -> BoolTerm:
        self._expect_bool(x, tag.symbol)
        return self._bool_term(self._push_raw(tag, 0, [x._ref]))

    def _bool_binary(self, tag: Op, a: BoolTerm, b: BoolTerm) -> BoolTerm:
        self._expect_bool(a, tag.symbol)
        if not isinstance(b, BoolTerm):
            raise SortError(f"{tag.symbol}: expected Bool term, got {type(b).__name__}")
        self._expect_bool(b, tag.symbol)
        return self._bool_term(self._push_raw(tag, 0, [a._ref, b._ref]))

    def _extend(self, tag: Op, x: BVTerm, amount: int) -> BVTerm:
        if not 0 <= amount <= 0xFFFF:
            raise WidthMismatchError(f"{tag.symbol}: invalid extension amount {amount}")
        width = self._expect_bv(x, tag.symbol) + amount
        self._check_bv_width(width, context=f"{tag.symbol} result")
        return self._bv_term(self._push_raw(tag, width, [x._ref], amount))

    def _mark(self, ref: int, live: set[int]) -> None:
        idx = _ref_index(ref)
        if idx >= len(self._nodes):
            raise ProtocolError(f"bad root reference #{idx}")
        if idx in live:
            return
        live.add(idx)
        node = self._nodes[idx]
        for i in range(node.arity):
            self._mark(self._children[node.children + i], live)

    def _compact(
        self, roots: list[int]
    ) -> tuple[bytes, dict[int, int], dict[int, int]]:
        live: set[int] = set()
        for root in roots:
            self._mark(root, live)
        old_to_new: dict[int, int] = {}
        new_to_old: dict[int, int] = {}
        new_nodes: list[Node] = []
        new_children: list[int] = []
        for old, node in enumerate(self._nodes):
            if old in live:
                sort = self._tag_sort(node.tag)
                new_ref = (
                    _bool_ref(len(new_nodes))
                    if sort is Sort.BOOL
                    else _bv_ref(len(new_nodes))
                )
                old_ref = _bool_ref(old) if sort is Sort.BOOL else _bv_ref(old)
                old_to_new[old] = new_ref
                new_to_old[new_ref] = old_ref
                new_nodes.append(node)
        for old, node in enumerate(self._nodes):
            if old not in live:
                continue
            start = len(new_children) if node.arity else 0
            for i in range(node.arity):
                child = self._children[node.children + i]
                new_children.append(old_to_new[_ref_index(child)])
            new_nodes[_ref_index(old_to_new[old])] = Node(
                node.tag,
                node.arity,
                node.aux_hi,
                node.width,
                node.aux_lo,
                start,
                node.payload,
            )
        return (
            self._expr_bytes(new_nodes, new_children, self._blob),
            old_to_new,
            new_to_old,
        )

    def _expr_bytes(
        self, nodes: list[Node], children: list[int], blob: bytes | bytearray
    ) -> bytes:
        out = bytearray(
            EXPR_MAGIC
            + bytes([VERSION, 0, 0, 0])
            + struct.pack("<III", len(nodes), len(children), len(blob))
            + bytes(12)
        )
        for n in nodes:
            out.extend(
                struct.pack(
                    "<BBHIIIQ",
                    int(n.tag),
                    n.arity,
                    n.aux_hi,
                    n.width,
                    n.aux_lo,
                    n.children,
                    n.payload,
                )
            )
        for child in children:
            out.extend(struct.pack("<I", child))
        out.extend(blob)
        return bytes(out)

    def _build_solve_request(
        self,
        request_id: int,
        budget_ms: int = 0,
        want_model: bool = True,
        want_core: bool = False,
    ) -> _Request:
        flags = (RequestFlag.WANT_MODEL if want_model else 0) | (
            RequestFlag.WANT_CORE if want_core else 0
        )
        return self._build_request(
            request_id, Command.SOLVE, int(flags), budget_ms, None
        )

    def _build_simplify_request(self, request_id: int, target: Term) -> _Request:
        target = self._expect_term(target, "simplify")
        return self._build_request(request_id, Command.SIMPLIFY, 0, 0, target)

    def _build_minimize_request(
        self,
        request_id: int,
        target: BVTerm,
        signed: bool = False,
        budget_ms: int = 0,
        want_model: bool = True,
    ) -> _Request:
        self._expect_bv(target, "minimize")
        flags = (RequestFlag.SIGNED if signed else 0) | (
            RequestFlag.WANT_MODEL if want_model else 0
        )
        return self._build_request(
            request_id, Command.MINIMIZE, int(flags), budget_ms, target
        )

    def _build_maximize_request(
        self,
        request_id: int,
        target: BVTerm,
        signed: bool = False,
        budget_ms: int = 0,
        want_model: bool = True,
    ) -> _Request:
        self._expect_bv(target, "maximize")
        flags = (RequestFlag.SIGNED if signed else 0) | (
            RequestFlag.WANT_MODEL if want_model else 0
        )
        return self._build_request(
            request_id, Command.MAXIMIZE, int(flags), budget_ms, target
        )

    def _build_request(
        self,
        request_id: int,
        command: Command,
        flags: int,
        budget_ms: int,
        target: Optional[Term],
    ) -> _Request:
        if not 0 <= request_id <= 0xFFFFFFFF:
            raise ProtocolError("request_id must fit in u32")
        if not 0 <= budget_ms <= 0xFFFFFFFF:
            raise ProtocolError("budget_ms must fit in u32")
        if command is Command.SIMPLIFY:
            if target is None:
                raise ProtocolError("SIMPLIFY requires a target expression")
            assertions: list[_Assertion] = []
            named: list[_Assertion] = []
            assumptions: list[int] = []
        else:
            named = [a for a in self._assertions if a.name is not None]
            unnamed = [a for a in self._assertions if a.name is None]
            assertions = named + unnamed
            assumptions = list(self._assumptions)
        roots = (
            [a.root for a in assertions]
            + assumptions
            + ([target._ref] if target is not None else [])
        )
        expr, old_to_new, new_to_old = self._compact(roots)
        assertion_roots = [old_to_new[_ref_index(a.root)] for a in assertions]
        assumption_roots = [old_to_new[_ref_index(a)] for a in assumptions]
        target_raw = old_to_new[_ref_index(target._ref)] if target is not None else 0
        out = bytearray(
            REQUEST_MAGIC
            + struct.pack("<I", request_id)
            + bytes([int(command), flags])
            + struct.pack("<I", budget_ms)
            + struct.pack("<I", len(expr))
            + struct.pack(
                "<HHH", len(assertion_roots), len(named), len(assumption_roots)
            )
            + struct.pack("<I", target_raw)
            + bytes(4)
        )
        out.extend(expr)
        for root in assertion_roots:
            out.extend(struct.pack("<I", root))
        for assertion in named:
            assert assertion.name is not None
            out.extend(struct.pack("<II", assertion.name[0], assertion.name[1]))
        for root in assumption_roots:
            out.extend(struct.pack("<I", root))
        return _Request(bytes(out), command, self, old_to_new, new_to_old, target)

    def _term_to_smt2(self, term: Term, depth: int) -> str:
        self._expect_term(term, "to_smt2")
        if depth < -1:
            raise ValueError("depth must be -1 or non-negative")
        rendered = self._render_smt2(
            term._ref, None if depth == -1 else depth, root=True
        )
        return f"{rendered} ; #{term.id}"

    def _render_smt2(
        self, ref: int, remaining: Optional[int], root: bool = False
    ) -> str:
        idx = _ref_index(ref)
        node = self._nodes[idx]
        if (
            remaining is not None
            and not root
            and remaining < 0
            and not self._is_atom(node)
        ):
            return f"|#{idx}|"
        next_remaining = None if remaining is None else remaining - 1
        child_refs = [self._children[node.children + i] for i in range(node.arity)]
        children = [self._render_smt2(child, next_remaining) for child in child_refs]
        tag = node.tag
        if tag == Op.BV_VAR or tag == Op.BOOL_VAR:
            return self._quote_symbol(self._blob_bytes(node.payload).decode("utf-8"))
        if tag == Op.BV_CONST:
            return self._format_bv_const(node)
        if tag == Op.BOOL_TRUE:
            return "true"
        if tag == Op.BOOL_FALSE:
            return "false"
        if tag == Op.BV_EXTRACT:
            return f"((_ extract {node.aux_hi} {node.aux_lo}) {children[0]})"
        if tag == Op.BV_CONCAT:
            return f"(concat {children[0]} {children[1]})"
        if tag == Op.BV_ZEXT:
            return f"((_ zero_extend {node.aux_hi}) {children[0]})"
        if tag == Op.BV_SEXT:
            return f"((_ sign_extend {node.aux_hi}) {children[0]})"
        if tag == Op.BV_ITE:
            return f"(ite {children[0]} {children[1]} {children[2]})"
        if tag == Op.BV_SELECT:
            pair_count = node.aux_hi
            expr = children[-1]
            for i in range(pair_count - 1, -1, -1):
                expr = f"(ite {children[2 * i]} {children[2 * i + 1]} {expr})"
            return expr
        if node.arity == 1:
            return f"({tag.symbol} {children[0]})"
        if node.arity == 2:
            return f"({tag.symbol} {children[0]} {children[1]})"
        return f"(|tag#{tag}| {' '.join(children)})"

    def _is_atom(self, node: Node) -> bool:
        return node.tag in _ATOM_OPS

    def _blob_bytes(self, payload: int) -> bytes:
        offset, length = _blob_ref(payload)
        if offset + length > len(self._blob):
            raise ProtocolError("blob reference out of range")
        return bytes(self._blob[offset : offset + length])

    def _bv_const_value(self, node: Node) -> int:
        if node.tag != Op.BV_CONST:
            raise ProtocolError("internal error: expected Op.BV_CONST node")
        if node.width <= 64:
            return node.payload & (
                (1 << node.width) - 1 if node.width < 64 else (1 << 64) - 1
            )
        return int.from_bytes(self._blob_bytes(node.payload), "little") & (
            (1 << node.width) - 1
        )

    def _format_bv_const(self, node: Node) -> str:
        value = self._bv_const_value(node)
        if node.width % 4 == 0:
            return f"#x{value:0{node.width // 4}x}"
        return f"#b{value:0{node.width}b}"

    def _quote_symbol(self, name: str) -> str:
        if (
            _SIMPLE_SYMBOL.match(name)
            and name not in _RESERVED_SYMBOLS
            and not name.startswith("#")
        ):
            return name
        return "|" + name.replace("\\", "\\\\").replace("|", "\\|") + "|"

    @classmethod
    def _from_expr_bytes(cls, data: bytes) -> Context:
        ctx = cls()
        if len(data) < 32 or data[:4] != EXPR_MAGIC:
            raise ProtocolError("bad expression buffer")
        if data[4] != VERSION:
            raise ProtocolError(f"unsupported expression version {data[4]}")
        node_count, child_count, blob_len = struct.unpack_from("<III", data, 8)
        expected = 32 + node_count * 24 + child_count * 4 + blob_len
        if len(data) != expected:
            raise ProtocolError("expression length mismatch")
        node_off = 32
        child_off = node_off + node_count * 24
        blob_off = child_off + child_count * 4
        for i in range(node_count):
            tag_raw, arity, aux_hi, width, aux_lo, children, payload = (
                struct.unpack_from("<BBHIIIQ", data, node_off + i * 24)
            )
            try:
                tag = Op(tag_raw)
            except ValueError as exc:
                raise ProtocolError(
                    f"unknown node tag {tag_raw} in expression buffer"
                ) from exc
            node = Node(tag, arity, aux_hi, width, aux_lo, children, payload)
            ctx._nodes.append(node)
        for i in range(child_count):
            (child,) = struct.unpack_from("<I", data, child_off + i * 4)
            ctx._children.append(child)
        ctx._blob.extend(data[blob_off : blob_off + blob_len])
        for idx, node in enumerate(ctx._nodes):
            if node.arity and node.children + node.arity > len(ctx._children):
                raise ProtocolError(f"node #{idx} child range out of bounds")
            for i in range(node.arity):
                ctx._meta_for_ref(ctx._children[node.children + i])
        return ctx


class Model:
    def __init__(self, ctx: Context, values: dict[int, ScalarValue]) -> None:
        self._ctx = ctx
        self._values = dict(values)

    @property
    def context(self) -> Context:
        return self._ctx

    def __len__(self) -> int:
        return len(self._values)

    def __contains__(self, term: object) -> bool:
        return (
            isinstance(term, Term)
            and term.context is self._ctx
            and term._ref in self._values
        )

    def __getitem__(self, term: Term) -> ScalarValue:
        if not isinstance(term, Term):
            raise KeyError(term)
        if term.context is not self._ctx:
            raise ContextMismatchError(
                f"model belongs to {self._ctx}, got term from {term.context}"
            )
        return self._values[term._ref]

    def get(
        self, term: Term, default: Optional[ScalarValue] = None
    ) -> Optional[ScalarValue]:
        if not isinstance(term, Term) or term.context is not self._ctx:
            return default
        return self._values.get(term._ref, default)

    def __iter__(self) -> Iterator[Term]:
        for ref in self._values:
            yield self._ctx._term(ref)

    def items(self) -> Iterator[tuple[Term, ScalarValue]]:
        for ref, value in self._values.items():
            yield self._ctx._term(ref), value

    def values(self) -> Iterator[ScalarValue]:
        return iter(self._values.values())

    def __repr__(self) -> str:
        return f"Model({self._ctx}, entries={len(self._values)})"


@dataclass(frozen=True)
class Response:
    request_id: int
    status: Status
    flags: ResponseFlag
    message: Optional[str] = None
    model: Optional[Model] = None
    core: Optional[list[str]] = None


@dataclass(frozen=True)
class SimplifyResult:
    request_id: int
    status: Status
    message: Optional[str] = None
    context: Optional[Context] = None
    term: Optional[Term] = None


@dataclass(frozen=True)
class OptimizationResult:
    request_id: int
    status: Status
    flags: ResponseFlag
    message: Optional[str] = None
    optimum: Optional[ScalarValue] = None
    model: Optional[Model] = None


class Client:
    """Blocking TCP client for the SMT server transport."""

    def __init__(
        self,
        host: str = "127.0.0.1",
        port: int = 9123,
        timeout: Optional[float] = None,
        sock: Optional[socket.socket] = None,
        max_response_bytes: int = DEFAULT_MAX_RESPONSE_BYTES,
    ) -> None:
        if max_response_bytes < 0:
            raise ValueError("max_response_bytes must be non-negative")
        self.max_response_bytes = max_response_bytes
        self._request_ids = itertools.count(1)
        self._sock = (
            sock
            if sock is not None
            else socket.create_connection((host, port), timeout=timeout)
        )
        if timeout is not None:
            self._sock.settimeout(timeout)

    @classmethod
    def from_socket(cls, sock: socket.socket) -> Client:
        return cls(sock=sock)

    def set_max_response_bytes(self, max_response_bytes: int) -> None:
        if max_response_bytes < 0:
            raise ValueError("max_response_bytes must be non-negative")
        self.max_response_bytes = max_response_bytes

    def set_timeout(self, timeout: Optional[float]) -> None:
        self._sock.settimeout(timeout)

    def close(self) -> None:
        self._sock.close()

    def __enter__(self) -> Client:
        return self

    def __exit__(self, *exc_info: object) -> None:
        self.close()

    def solve(
        self,
        ctx: Context,
        *,
        request_id: Optional[int] = None,
        budget_ms: int = 0,
        want_model: bool = True,
        want_core: bool = False,
    ) -> Response:
        request = ctx._build_solve_request(
            self._request_id(request_id), budget_ms, want_model, want_core
        )
        raw = self._send_binary(request.payload)
        return self._solve_response(raw, request)

    def simplify(
        self, term: Term, *, request_id: Optional[int] = None
    ) -> SimplifyResult:
        request = term.context._build_simplify_request(
            self._request_id(request_id), term
        )
        raw = self._send_binary(request.payload)
        return self._simplify_response(raw)

    def minimize(
        self,
        target: BVTerm,
        *,
        request_id: Optional[int] = None,
        signed: bool = False,
        budget_ms: int = 0,
        want_model: bool = True,
    ) -> OptimizationResult:
        request = target.context._build_minimize_request(
            self._request_id(request_id), target, signed, budget_ms, want_model
        )
        raw = self._send_binary(request.payload)
        return self._optimization_response(raw, request)

    def maximize(
        self,
        target: BVTerm,
        *,
        request_id: Optional[int] = None,
        signed: bool = False,
        budget_ms: int = 0,
        want_model: bool = True,
    ) -> OptimizationResult:
        request = target.context._build_maximize_request(
            self._request_id(request_id), target, signed, budget_ms, want_model
        )
        raw = self._send_binary(request.payload)
        return self._optimization_response(raw, request)

    def smt2(self, script: str) -> str:
        if not isinstance(script, str):
            raise TypeError(f"smt2: expected str, got {type(script).__name__}")
        return self._send_payload(script.encode("utf-8")).decode("utf-8")

    def _request_id(self, request_id: Optional[int]) -> int:
        if request_id is None:
            return next(self._request_ids)
        if not 0 <= request_id <= 0xFFFFFFFF:
            raise ProtocolError("request_id must fit in u32")
        return request_id

    def _send_payload(self, payload: bytes) -> bytes:
        self._sock.sendall(_frame(payload))
        (length,) = struct.unpack("<I", _recv_exact(self._sock, 4))
        if length > self.max_response_bytes:
            raise ProtocolError(
                f"response frame length {length} exceeds configured maximum {self.max_response_bytes}"
            )
        return _recv_exact(self._sock, length)

    def _send_binary(self, request: bytes) -> _RawResponse:
        return _parse_response(self._send_payload(request))

    def _solve_response(self, raw: _RawResponse, request: _Request) -> Response:
        if raw.status is Status.ERROR:
            return Response(
                raw.request_id, raw.status, raw.flags, message=raw.message()
            )
        if raw.status is Status.UNKNOWN:
            return Response(
                raw.request_id,
                raw.status,
                raw.flags,
                message=raw.message() if raw.flags & ResponseFlag.HAS_MESSAGE else None,
            )
        if raw.status is Status.SAT:
            if raw.flags & ResponseFlag.HAS_VALUE:
                raise ProtocolError(
                    "solve response unexpectedly contained optimization value"
                )
            model = (
                self._model_from_entries(_parse_model(raw.payload), request)
                if raw.flags & ResponseFlag.HAS_MODEL
                else None
            )
            return Response(raw.request_id, raw.status, raw.flags, model=model)
        if raw.status is Status.UNSAT:
            core = (
                _parse_core(raw.payload) if raw.flags & ResponseFlag.HAS_CORE else None
            )
            return Response(raw.request_id, raw.status, raw.flags, core=core)
        raise ProtocolError("solve response unexpectedly used SIMPLIFIED status")

    def _simplify_response(self, raw: _RawResponse) -> SimplifyResult:
        if raw.status is Status.ERROR:
            return SimplifyResult(raw.request_id, raw.status, message=raw.message())
        if raw.status is Status.UNKNOWN:
            return SimplifyResult(
                raw.request_id,
                raw.status,
                message=raw.message() if raw.flags & ResponseFlag.HAS_MESSAGE else None,
            )
        if raw.status is not Status.SIMPLIFIED:
            raise ProtocolError(
                f"simplify response unexpectedly used {raw.status.name}"
            )
        block = _parse_simplify(raw.payload)
        ctx = Context._from_expr_bytes(block.expression)
        term = ctx._term(block.target_node)
        return SimplifyResult(raw.request_id, raw.status, context=ctx, term=term)

    def _optimization_response(
        self, raw: _RawResponse, request: _Request
    ) -> OptimizationResult:
        if raw.status is Status.ERROR:
            return OptimizationResult(
                raw.request_id, raw.status, raw.flags, message=raw.message()
            )
        if raw.status is Status.UNKNOWN:
            return OptimizationResult(
                raw.request_id,
                raw.status,
                raw.flags,
                message=raw.message() if raw.flags & ResponseFlag.HAS_MESSAGE else None,
            )
        if raw.status is Status.UNSAT:
            if raw.flags != 0:
                raise ProtocolError(
                    "optimization UNSAT response unexpectedly contained payload"
                )
            return OptimizationResult(raw.request_id, raw.status, raw.flags)
        if raw.status is not Status.SAT:
            raise ProtocolError(
                f"optimization response unexpectedly used {raw.status.name}"
            )
        if not raw.flags & ResponseFlag.HAS_VALUE:
            raise ProtocolError("optimization SAT response missing value")
        block = _parse_optimization(
            raw.payload, bool(raw.flags & ResponseFlag.HAS_MODEL)
        )
        model = (
            self._model_from_entries(block.model_entries or [], request)
            if block.model_entries is not None
            else None
        )
        return OptimizationResult(
            raw.request_id, raw.status, raw.flags, optimum=block.optimum, model=model
        )

    def _model_from_entries(
        self, entries: list[_RawModelEntry], request: _Request
    ) -> Model:
        values: dict[int, ScalarValue] = {}
        for entry in entries:
            old_ref = request.new_to_old.get(entry.node_ref)
            if old_ref is None:
                raise ProtocolError(
                    f"model contains unknown compacted node ref {entry.node_ref:#x}"
                )
            meta = request.context._meta_for_ref(old_ref)
            node = request.context._nodes[_ref_index(old_ref)]
            if meta.sort is Sort.BOOL:
                if node.tag != Op.BOOL_VAR or entry.value.width != 0:
                    raise ProtocolError(
                        "model Bool entry does not match a Bool variable"
                    )
            elif node.tag != Op.BV_VAR or entry.value.width != meta.width:
                raise ProtocolError("model BV entry does not match a BV variable")
            values[old_ref] = entry.value
        return Model(request.context, values)


def _frame(payload: bytes) -> bytes:
    if len(payload) > 0xFFFFFFFF:
        raise ProtocolError("frame payload too large")
    return struct.pack("<I", len(payload)) + payload


def _recv_exact(sock: socket.socket, length: int) -> bytes:
    chunks: list[bytes] = []
    remaining = length
    while remaining:
        chunk = sock.recv(remaining)
        if not chunk:
            raise EOFError("socket closed while reading frame")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def _need(data: bytes, offset: int, length: int, context: str) -> None:
    if offset + length > len(data):
        raise ProtocolError(f"short {context}")


def _parse_response(data: bytes) -> _RawResponse:
    if len(data) < 16 or data[:4] != RESPONSE_MAGIC:
        raise ProtocolError("bad response envelope")
    (request_id,) = struct.unpack_from("<I", data, 4)
    try:
        status = Status(data[8])
    except ValueError as exc:
        raise ProtocolError(f"unknown response status {data[8]}") from exc
    flags = ResponseFlag(data[9])
    (payload_len,) = struct.unpack_from("<I", data, 10)
    (reserved,) = struct.unpack_from("<H", data, 14)
    if reserved != 0:
        raise ProtocolError("response reserved field is not zero")
    if len(data) != 16 + payload_len:
        raise ProtocolError("response length mismatch")
    payload = data[16:]
    _validate_response_shape(status, flags, payload)
    return _RawResponse(request_id, status, flags, payload)


def _validate_response_shape(
    status: Status, flags: ResponseFlag, payload: bytes
) -> None:
    if int(flags) & ~ResponseFlag.all_bits():
        raise ProtocolError("unknown response flag bits")
    if status is Status.ERROR:
        if flags != ResponseFlag.HAS_MESSAGE:
            raise ProtocolError("ERROR status must use exactly HAS_MESSAGE")
        payload.decode("utf-8")
    elif status is Status.UNKNOWN:
        if flags == 0:
            if payload:
                raise ProtocolError("UNKNOWN payload requires HAS_MESSAGE")
        elif flags == ResponseFlag.HAS_MESSAGE:
            payload.decode("utf-8")
        else:
            raise ProtocolError("UNKNOWN status may only use HAS_MESSAGE")
    elif status is Status.SAT:
        allowed = ResponseFlag.HAS_MODEL | ResponseFlag.HAS_VALUE
        if flags & ~allowed:
            raise ProtocolError("SAT status may only use HAS_MODEL/HAS_VALUE")
        if flags == 0 and payload:
            raise ProtocolError("SAT payload without flags")
    elif status is Status.UNSAT:
        if flags == 0:
            if payload:
                raise ProtocolError("UNSAT payload without HAS_CORE")
        elif flags != ResponseFlag.HAS_CORE:
            raise ProtocolError("UNSAT status may only use HAS_CORE")
    elif status is Status.SIMPLIFIED:
        if flags != ResponseFlag.HAS_EXPR:
            raise ProtocolError("SIMPLIFIED status must use exactly HAS_EXPR")


def _parse_scalar(data: bytes, offset: int = 0) -> tuple[ScalarValue, int]:
    _need(data, offset, 8, "scalar header")
    width, value_len = struct.unpack_from("<II", data, offset)
    offset += 8
    _need(data, offset, value_len, "scalar value")
    raw = bytes(data[offset : offset + value_len])
    offset += value_len
    if width == 0:
        if value_len != 1 or raw[0] not in (0, 1):
            raise ProtocolError("invalid Bool scalar")
    else:
        expected = _bytes_for_width(width)
        if value_len != expected:
            raise ProtocolError("invalid BV scalar length")
        valid = width % 8
        if valid and raw and (raw[-1] & ~((1 << valid) - 1)):
            raise ProtocolError("unused high bits are set in BV scalar")
    return ScalarValue(width, raw), offset


def _parse_model(payload: bytes) -> list[_RawModelEntry]:
    _need(payload, 0, 4, "model header")
    (count,) = struct.unpack_from("<I", payload, 0)
    offset = 4
    entries: list[_RawModelEntry] = []
    for _ in range(count):
        _need(payload, offset, 4, "model node_ref")
        (node_ref,) = struct.unpack_from("<I", payload, offset)
        offset += 4
        value, offset = _parse_scalar(payload, offset)
        entries.append(_RawModelEntry(node_ref, value))
    if offset != len(payload):
        raise ProtocolError("trailing bytes in model block")
    return entries


def _parse_core(payload: bytes) -> list[str]:
    _need(payload, 0, 4, "unsat core header")
    (count,) = struct.unpack_from("<I", payload, 0)
    offset = 4
    names: list[str] = []
    for _ in range(count):
        _need(payload, offset, 4, "unsat core name length")
        (length,) = struct.unpack_from("<I", payload, offset)
        offset += 4
        _need(payload, offset, length, "unsat core name")
        names.append(payload[offset : offset + length].decode("utf-8"))
        offset += length
    if offset != len(payload):
        raise ProtocolError("trailing bytes in unsat core block")
    return names


def _parse_simplify(payload: bytes) -> _SimplifyBlock:
    _need(payload, 0, 8, "simplify header")
    expr_len, target_node = struct.unpack_from("<II", payload, 0)
    offset = 8
    _need(payload, offset, expr_len, "simplify expression")
    expression = bytes(payload[offset : offset + expr_len])
    offset += expr_len
    if offset != len(payload):
        raise ProtocolError("trailing bytes in simplify block")
    return _SimplifyBlock(expression, target_node)


def _parse_optimization(payload: bytes, has_model: bool = False) -> _OptimizationBlock:
    optimum, offset = _parse_scalar(payload, 0)
    model = None
    if has_model:
        model = _parse_model(payload[offset:])
        offset = len(payload)
    if offset != len(payload):
        raise ProtocolError("trailing bytes in optimization block")
    return _OptimizationBlock(optimum, model)


__all__ = [
    "Context",
    "Client",
    "Term",
    "BVTerm",
    "BoolTerm",
    "Status",
    "Sort",
    "Op",
    "Command",
    "RequestFlag",
    "ResponseFlag",
    "ScalarValue",
    "Model",
    "Response",
    "SimplifyResult",
    "OptimizationResult",
    "SmtError",
    "SortError",
    "WidthMismatchError",
    "ContextMismatchError",
    "ProtocolError",
    "DEFAULT_MAX_RESPONSE_BYTES",
]
