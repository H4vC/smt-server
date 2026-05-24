"""Experimental in-process Z3 server for the SMT v1 wire protocol.

The module is separate from ``smt_wire`` so the Python client remains usable
without Z3. Install the optional dependency with ``smt-wire[z3]`` before using
``Z3Server`` or running ``python -m smt_z3_server``.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import socket
import struct
import threading
import time
from typing import Any, Optional

import smt_wire as smt

BOOL_BIT = 0x80000000
INDEX_MASK = 0x7FFFFFFF
REQUEST_HEADER_SIZE = 32
DEFAULT_MAX_FRAME_BYTES = 64 * 1024 * 1024
DEFAULT_MAX_RESPONSE_BYTES = 64 * 1024 * 1024
DEFAULT_MAX_CONNECTIONS = 128

REQ_WANT_MODEL = int(smt.RequestFlag.WANT_MODEL)
REQ_WANT_CORE = int(smt.RequestFlag.WANT_CORE)
REQ_SIGNED = int(smt.RequestFlag.SIGNED)
REQ_ALL_FLAGS = REQ_WANT_MODEL | REQ_WANT_CORE | REQ_SIGNED

RESP_HAS_MODEL = int(smt.ResponseFlag.HAS_MODEL)
RESP_HAS_CORE = int(smt.ResponseFlag.HAS_CORE)
RESP_HAS_EXPR = int(smt.ResponseFlag.HAS_EXPR)
RESP_HAS_VALUE = int(smt.ResponseFlag.HAS_VALUE)
RESP_HAS_MESSAGE = int(smt.ResponseFlag.HAS_MESSAGE)


def _load_z3() -> Any:
    try:
        import z3  # type: ignore[import-not-found]
    except ImportError as exc:  # pragma: no cover - depends on environment
        raise ImportError(
            "smt_z3_server requires the optional z3 dependency; "
            "install with `pip install 'smt-wire[z3]'` or `pip install z3-solver`"
        ) from exc
    return z3


def _ref_index(ref: int) -> int:
    return ref & INDEX_MASK


def _is_bool_ref(ref: int) -> bool:
    return bool(ref & BOOL_BIT)


def _bv_ref(index: int) -> int:
    return index


def _bool_ref(index: int) -> int:
    return BOOL_BIT | index


def _blob_ref(payload: int) -> tuple[int, int]:
    return payload >> 32, payload & 0xFFFFFFFF


def _bytes_for_width(width: int) -> int:
    if not 1 <= width <= smt.MAX_WIDTH:
        raise smt.WidthMismatchError(f"invalid BV width {width}")
    return (width + 7) // 8


@dataclass(frozen=True)
class _BinaryRequest:
    payload: bytes
    request_id: int
    command: smt.Command
    flags: int
    budget_ms: int
    expression: bytes
    context: smt.Context
    assertion_roots: list[int]
    named_assertion_names: list[str]
    assumption_roots: list[int]
    target_node: int

    @property
    def want_model(self) -> bool:
        return bool(self.flags & REQ_WANT_MODEL)

    @property
    def want_core(self) -> bool:
        return bool(self.flags & REQ_WANT_CORE)

    @property
    def signed(self) -> bool:
        return bool(self.flags & REQ_SIGNED)


@dataclass(frozen=True)
class _Z3Variable:
    node_ref: int
    sort: smt.Sort
    width: int


@dataclass
class _Z3Translation:
    bvs: list[Optional[Any]]
    bools: list[Optional[Any]]
    variables: list[_Z3Variable]
    z3_ctx: Any

    def bv(self, ref: int) -> Any:
        if _is_bool_ref(ref):
            raise smt.ProtocolError("Z3 translation expected BV reference")
        index = _ref_index(ref)
        if index >= len(self.bvs) or self.bvs[index] is None:
            raise smt.ProtocolError(f"Z3 translation missing BV term #{index}")
        return self.bvs[index]

    def bool(self, ref: int) -> Any:
        if not _is_bool_ref(ref):
            raise smt.ProtocolError("Z3 translation expected Bool reference")
        index = _ref_index(ref)
        if index >= len(self.bools) or self.bools[index] is None:
            raise smt.ProtocolError(f"Z3 translation missing Bool term #{index}")
        return self.bools[index]


class _Deadline:
    def __init__(self, budget_ms: int) -> None:
        self._deadline = (
            time.monotonic() + budget_ms / 1000.0 if budget_ms else None
        )

    def remaining_ms(self) -> Optional[int]:
        if self._deadline is None:
            return None
        remaining = self._deadline - time.monotonic()
        if remaining <= 0:
            return 0
        return max(1, min(int(remaining * 1000), 0xFFFFFFFF))


class _Z3Backend:
    def __init__(self) -> None:
        self.z3 = _load_z3()

    def handle(self, request: _BinaryRequest) -> bytes:
        if request.command is smt.Command.SIMPLIFY:
            return _simplify_response(request)
        if request.command is smt.Command.SOLVE:
            return self._solve(request)
        if request.command in (smt.Command.MINIMIZE, smt.Command.MAXIMIZE):
            return self._optimize(request)
        raise smt.ProtocolError(f"unsupported command {request.command}")

    def _solve(self, request: _BinaryRequest) -> bytes:
        z3 = self.z3
        deadline = _Deadline(request.budget_ms)
        translation = _translate(request, z3)
        solver = z3.Solver(ctx=translation.z3_ctx)
        trackers: list[tuple[str, Any]] = []

        for index, root in enumerate(request.assertion_roots):
            assertion = translation.bool(root)
            if request.want_core and index < len(request.named_assertion_names):
                tracker = z3.Bool(f"core_{index}", ctx=translation.z3_ctx)
                solver.assert_and_track(assertion, tracker)
                trackers.append((request.named_assertion_names[index], tracker))
            else:
                solver.add(assertion)

        assumptions = [translation.bool(root) for root in request.assumption_roots]
        status = _check_with_deadline(z3, solver, assumptions, deadline)
        if status == z3.sat:
            payload = b""
            flags = 0
            if request.want_model:
                model = solver.model()
                payload = _encode_model(translation, model)
                flags |= RESP_HAS_MODEL
            return _response(request.request_id, smt.Status.SAT, flags, payload)
        if status == z3.unsat:
            payload = b""
            flags = 0
            if request.want_core:
                payload = _encode_core(_build_core(solver, trackers))
                flags |= RESP_HAS_CORE
            return _response(request.request_id, smt.Status.UNSAT, flags, payload)
        return _unknown_response(request.request_id, _unknown_reason(solver))

    def _optimize(self, request: _BinaryRequest) -> bytes:
        z3 = self.z3
        deadline = _Deadline(request.budget_ms)
        translation = _translate(request, z3)
        solver = z3.Solver(ctx=translation.z3_ctx)
        for root in request.assertion_roots:
            solver.add(translation.bool(root))

        fixed = [translation.bool(root) for root in request.assumption_roots]
        status = _check_with_deadline(z3, solver, fixed, deadline)
        if status == z3.unsat:
            return _response(request.request_id, smt.Status.UNSAT, 0, b"")
        if status != z3.sat:
            return _unknown_response(request.request_id, _unknown_reason(solver))

        target = translation.bv(request.target_node)
        width = target.size()
        optimum = bytearray(_bytes_for_width(width))
        minimize = request.command is smt.Command.MINIMIZE

        for bit in range(width - 1, -1, -1):
            sign_bit = bit == width - 1
            prefer_one = _optimization_prefers_one(
                signed=request.signed, minimize=minimize, sign_bit=sign_bit
            )
            bit_is_one = self.z3.Extract(bit, bit, target) == self.z3.BitVecVal(
                1, 1, ctx=translation.z3_ctx
            )
            first_try = bit_is_one if prefer_one else self.z3.Not(bit_is_one)
            status = _check_with_deadline(z3, solver, fixed + [first_try], deadline)
            if status == z3.sat:
                fixed.append(first_try)
                if prefer_one:
                    _set_bit(optimum, bit)
            elif status == z3.unsat:
                fixed.append(self.z3.Not(bit_is_one) if prefer_one else bit_is_one)
                if not prefer_one:
                    _set_bit(optimum, bit)
            else:
                return _unknown_response(request.request_id, _unknown_reason(solver))

        status = _check_with_deadline(z3, solver, fixed, deadline)
        if status == z3.unsat:
            return _response(request.request_id, smt.Status.UNSAT, 0, b"")
        if status != z3.sat:
            return _unknown_response(request.request_id, _unknown_reason(solver))

        flags = RESP_HAS_VALUE
        payload = _encode_scalar_bv(width, bytes(optimum))
        if request.want_model:
            payload += _encode_model(translation, solver.model())
            flags |= RESP_HAS_MODEL
        return _response(request.request_id, smt.Status.SAT, flags, payload)


class Z3Server:
    """Small TCP server backed only by the Python ``z3-solver`` package.

    ``port=0`` asks the operating system for a free local port. The selected
    port is available through ``server.port`` after ``start`` returns.
    """

    def __init__(
        self,
        listener: socket.socket,
        backend: _Z3Backend,
        *,
        max_frame_bytes: int = DEFAULT_MAX_FRAME_BYTES,
        max_response_bytes: int = DEFAULT_MAX_RESPONSE_BYTES,
        max_connections: int = DEFAULT_MAX_CONNECTIONS,
    ) -> None:
        sockname = listener.getsockname()
        self.host = str(sockname[0])
        self.port = int(sockname[1])
        self._listener = listener
        self._backend = backend
        self._max_frame_bytes = max_frame_bytes
        self._max_response_bytes = max_response_bytes
        self._max_connections = max_connections
        self._stopped = threading.Event()
        self._lock = threading.Lock()
        self._connections: set[socket.socket] = set()
        self._connection_threads: list[threading.Thread] = []
        self._serve_error: Optional[BaseException] = None
        self._thread = threading.Thread(
            target=self._serve,
            name=f"smt-z3-server-{self.host}:{self.port}",
            daemon=True,
        )

    @classmethod
    def start(
        cls,
        host: str = smt.DEFAULT_SERVER_HOST,
        port: int = 0,
        *,
        max_frame_bytes: int = DEFAULT_MAX_FRAME_BYTES,
        max_response_bytes: int = DEFAULT_MAX_RESPONSE_BYTES,
        max_connections: int = DEFAULT_MAX_CONNECTIONS,
    ) -> "Z3Server":
        if not 0 <= port <= 65535:
            raise ValueError("port must fit in u16")
        if max_frame_bytes < 0 or max_response_bytes < 0:
            raise ValueError("frame and response limits must be non-negative")
        if max_connections < 1:
            raise ValueError("max_connections must be at least one")
        backend = _Z3Backend()
        listener = _bind_listener(host, port)
        listener.settimeout(0.1)
        server = cls(
            listener,
            backend,
            max_frame_bytes=max_frame_bytes,
            max_response_bytes=max_response_bytes,
            max_connections=max_connections,
        )
        server._thread.start()
        return server

    @property
    def address(self) -> tuple[str, int]:
        return self.host, self.port

    @property
    def server_address(self) -> str:
        if ":" in self.host and not self.host.startswith("["):
            return f"[{self.host}]:{self.port}"
        return f"{self.host}:{self.port}"

    def client(
        self,
        *,
        timeout: Optional[float] = None,
        max_response_bytes: int = smt.DEFAULT_MAX_RESPONSE_BYTES,
    ) -> smt.Client:
        return smt.Client(
            self.host,
            self.port,
            timeout=timeout,
            max_response_bytes=max_response_bytes,
        )

    def stop(self) -> None:
        if self._stopped.is_set():
            return
        self._stopped.set()
        try:
            self._listener.close()
        except OSError:
            pass
        with self._lock:
            connections = list(self._connections)
            threads = list(self._connection_threads)
        for conn in connections:
            try:
                conn.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                conn.close()
            except OSError:
                pass
        if threading.current_thread() is not self._thread:
            self._thread.join(timeout=2.0)
        for thread in threads:
            if threading.current_thread() is not thread:
                thread.join(timeout=2.0)

    def __enter__(self) -> "Z3Server":
        return self

    def __exit__(self, *exc_info: object) -> None:
        self.stop()

    def _serve(self) -> None:
        try:
            while not self._stopped.is_set():
                try:
                    conn, _addr = self._listener.accept()
                except socket.timeout:
                    continue
                except OSError:
                    if self._stopped.is_set():
                        return
                    raise
                if not self._register_connection(conn):
                    _safe_send(conn, _frame(_error_response(0, "maximum active connections reached")))
                    conn.close()
                    continue
                thread = threading.Thread(
                    target=self._handle_connection,
                    args=(conn,),
                    name=f"smt-z3-client-{self.host}:{self.port}",
                    daemon=True,
                )
                with self._lock:
                    self._connection_threads.append(thread)
                thread.start()
        except BaseException as exc:  # pragma: no cover - defensive bookkeeping
            self._serve_error = exc

    def _register_connection(self, conn: socket.socket) -> bool:
        with self._lock:
            if len(self._connections) >= self._max_connections:
                return False
            self._connections.add(conn)
            return True

    def _unregister_connection(self, conn: socket.socket) -> None:
        with self._lock:
            self._connections.discard(conn)

    def _handle_connection(self, conn: socket.socket) -> None:
        try:
            while not self._stopped.is_set():
                length_bytes = _recv_exact_or_none(conn, 4)
                if length_bytes is None:
                    return
                (frame_len,) = struct.unpack("<I", length_bytes)
                if frame_len > self._max_frame_bytes:
                    response = _error_response(
                        0,
                        f"frame payload length {frame_len} exceeds configured maximum {self._max_frame_bytes}",
                    )
                    _safe_send(conn, _frame(response))
                    return
                payload = _recv_exact(conn, frame_len)
                response = self._dispatch_payload(payload)
                if len(response) > self._max_response_bytes:
                    response = _error_response(
                        0,
                        f"response payload length {len(response)} exceeds configured maximum {self._max_response_bytes}",
                    )
                _safe_send(conn, _frame(response))
        except (EOFError, OSError):
            return
        finally:
            self._unregister_connection(conn)
            try:
                conn.close()
            except OSError:
                pass

    def _dispatch_payload(self, payload: bytes) -> bytes:
        if not payload.startswith(smt.REQUEST_MAGIC):
            return _text_error("Python Z3 server only supports binary SMTQ frames")
        try:
            request = _parse_binary_request(payload)
        except Exception as exc:
            return _error_response(0, str(exc))
        try:
            return self._backend.handle(request)
        except Exception as exc:
            return _error_response(request.request_id, str(exc))


def start_z3_server(
    host: str = smt.DEFAULT_SERVER_HOST,
    port: int = 0,
    *,
    max_frame_bytes: int = DEFAULT_MAX_FRAME_BYTES,
    max_response_bytes: int = DEFAULT_MAX_RESPONSE_BYTES,
    max_connections: int = DEFAULT_MAX_CONNECTIONS,
) -> Z3Server:
    return Z3Server.start(
        host,
        port,
        max_frame_bytes=max_frame_bytes,
        max_response_bytes=max_response_bytes,
        max_connections=max_connections,
    )


def _bind_listener(host: str, port: int) -> socket.socket:
    last_error: Optional[OSError] = None
    for family, socktype, proto, _canonname, sockaddr in socket.getaddrinfo(
        host, port, type=socket.SOCK_STREAM
    ):
        sock = socket.socket(family, socktype, proto)
        try:
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.bind(sockaddr)
            sock.listen()
            return sock
        except OSError as exc:
            last_error = exc
            sock.close()
    if last_error is not None:
        raise last_error
    raise OSError(f"could not resolve bind address {host!r}:{port}")


def _parse_binary_request(payload: bytes) -> _BinaryRequest:
    if len(payload) < REQUEST_HEADER_SIZE or payload[:4] != smt.REQUEST_MAGIC:
        raise smt.ProtocolError("bad request envelope")
    request_id = struct.unpack_from("<I", payload, 4)[0]
    try:
        command = smt.Command(payload[8])
    except ValueError as exc:
        raise smt.ProtocolError(f"unknown request command {payload[8]}") from exc
    flags = payload[9]
    budget_ms = struct.unpack_from("<I", payload, 10)[0]
    expr_len = struct.unpack_from("<I", payload, 14)[0]
    assertion_count, named_count, assumption_count = struct.unpack_from(
        "<HHH", payload, 18
    )
    target_node = struct.unpack_from("<I", payload, 24)[0]
    reserved = struct.unpack_from("<I", payload, 28)[0]
    if reserved != 0:
        raise smt.ProtocolError("request reserved field is not zero")
    if flags & ~REQ_ALL_FLAGS:
        raise smt.ProtocolError("unknown request flag bits")
    if named_count > assertion_count:
        raise smt.ProtocolError("named assertion count exceeds assertion count")

    offset = REQUEST_HEADER_SIZE
    expected = (
        REQUEST_HEADER_SIZE
        + expr_len
        + assertion_count * 4
        + named_count * 8
        + assumption_count * 4
    )
    if len(payload) != expected:
        raise smt.ProtocolError("request length mismatch")
    expression = bytes(payload[offset : offset + expr_len])
    offset += expr_len
    ctx = smt.Context._from_expr_bytes(expression)

    assertion_roots: list[int] = []
    for _ in range(assertion_count):
        (root,) = struct.unpack_from("<I", payload, offset)
        offset += 4
        _expect_ref(ctx, root, smt.Sort.BOOL, "assertion root")
        assertion_roots.append(root)

    named_assertion_names: list[str] = []
    for _ in range(named_count):
        name_offset, name_len = struct.unpack_from("<II", payload, offset)
        offset += 8
        name = _blob_bytes(ctx, name_offset, name_len, "named assertion").decode("utf-8")
        named_assertion_names.append(name)

    assumption_roots: list[int] = []
    for _ in range(assumption_count):
        (root,) = struct.unpack_from("<I", payload, offset)
        offset += 4
        _expect_ref(ctx, root, smt.Sort.BOOL, "assumption root")
        assumption_roots.append(root)

    if command is smt.Command.SOLVE:
        allowed = REQ_WANT_MODEL | REQ_WANT_CORE
        if flags & ~allowed:
            raise smt.ProtocolError("SOLVE only accepts WANT_MODEL/WANT_CORE")
        if target_node != 0:
            raise smt.ProtocolError("SOLVE requires target_node = 0")
    elif command is smt.Command.SIMPLIFY:
        if flags != 0:
            raise smt.ProtocolError("SIMPLIFY accepts no flags")
        if assertion_count or named_count or assumption_count:
            raise smt.ProtocolError("SIMPLIFY accepts no assertions or assumptions")
        _expect_ref(ctx, target_node, None, "simplify target")
    elif command in (smt.Command.MINIMIZE, smt.Command.MAXIMIZE):
        allowed = REQ_WANT_MODEL | REQ_SIGNED
        if flags & ~allowed:
            raise smt.ProtocolError("optimization only accepts WANT_MODEL/SIGNED")
        _expect_ref(ctx, target_node, smt.Sort.BV, "optimization target")
    else:  # pragma: no cover - enum exhaustiveness
        raise smt.ProtocolError(f"unsupported command {command}")

    if flags & REQ_WANT_CORE:
        seen: set[str] = set()
        for name in named_assertion_names:
            if name in seen:
                raise smt.ProtocolError(f"duplicate named assertion {name!r}")
            seen.add(name)

    return _BinaryRequest(
        payload=payload,
        request_id=request_id,
        command=command,
        flags=flags,
        budget_ms=budget_ms,
        expression=expression,
        context=ctx,
        assertion_roots=assertion_roots,
        named_assertion_names=named_assertion_names,
        assumption_roots=assumption_roots,
        target_node=target_node,
    )


def _expect_ref(
    ctx: smt.Context, ref: int, expected_sort: Optional[smt.Sort], context: str
) -> None:
    try:
        meta = ctx._meta_for_ref(ref)
    except smt.SmtError as exc:
        raise smt.ProtocolError(f"bad {context}: {exc}") from exc
    if expected_sort is not None and meta.sort is not expected_sort:
        raise smt.ProtocolError(
            f"bad {context}: expected {expected_sort.value}, got {meta.sort.value}"
        )


def _blob_bytes(ctx: smt.Context, offset: int, length: int, context: str) -> bytes:
    if offset > len(ctx._blob) or length > len(ctx._blob) - offset:
        raise smt.ProtocolError(f"{context} blob reference out of range")
    return bytes(ctx._blob[offset : offset + length])


def _translate(request: _BinaryRequest, z3: Any) -> _Z3Translation:
    ctx = request.context
    z3_ctx = z3.Context()
    out = _Z3Translation(
        bvs=[None] * len(ctx._nodes),
        bools=[None] * len(ctx._nodes),
        variables=[],
        z3_ctx=z3_ctx,
    )
    bv_vars: dict[tuple[str, int], Any] = {}
    bool_vars: dict[str, Any] = {}

    for index, node in enumerate(ctx._nodes):
        _validate_node_shape(node)
        tag = node.tag
        if tag is smt.Op.BV_VAR:
            name = _node_blob(ctx, node, "BV variable").decode("utf-8")
            term = bv_vars.get((name, node.width))
            if term is None:
                term = z3.BitVec(f"bv_{index}", node.width, ctx=z3_ctx)
                bv_vars[(name, node.width)] = term
            out.variables.append(_Z3Variable(_bv_ref(index), smt.Sort.BV, node.width))
            out.bvs[index] = term
        elif tag is smt.Op.BV_CONST:
            out.bvs[index] = _z3_bv_const(ctx, node, z3, z3_ctx)
        elif tag is smt.Op.BV_NOT:
            x = _child_bv(ctx, out, node, 0)
            out.bvs[index] = ~x
        elif tag is smt.Op.BV_NEG:
            x = _child_bv(ctx, out, node, 0)
            out.bvs[index] = -x
        elif tag is smt.Op.BV_AND:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a & b
        elif tag is smt.Op.BV_OR:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a | b
        elif tag is smt.Op.BV_XOR:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a ^ b
        elif tag is smt.Op.BV_ADD:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a + b
        elif tag is smt.Op.BV_SUB:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a - b
        elif tag is smt.Op.BV_MUL:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a * b
        elif tag is smt.Op.BV_UDIV:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = z3.UDiv(a, b)
        elif tag is smt.Op.BV_UREM:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = z3.URem(a, b)
        elif tag is smt.Op.BV_SDIV:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a / b
        elif tag is smt.Op.BV_SREM:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = z3.SRem(a, b)
        elif tag is smt.Op.BV_SMOD:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = _bvsmod(a, b, z3)
        elif tag is smt.Op.BV_SHL:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a << b
        elif tag is smt.Op.BV_LSHR:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = z3.LShR(a, b)
        elif tag is smt.Op.BV_ASHR:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = a >> b
        elif tag is smt.Op.BV_EXTRACT:
            x = _child_bv(ctx, out, node, 0)
            out.bvs[index] = z3.Extract(node.aux_hi, node.aux_lo, x)
        elif tag is smt.Op.BV_CONCAT:
            a, b = _child_bv2(ctx, out, node)
            out.bvs[index] = z3.Concat(a, b)
        elif tag is smt.Op.BV_ZEXT:
            x = _child_bv(ctx, out, node, 0)
            out.bvs[index] = z3.ZeroExt(node.aux_hi, x)
        elif tag is smt.Op.BV_SEXT:
            x = _child_bv(ctx, out, node, 0)
            out.bvs[index] = z3.SignExt(node.aux_hi, x)
        elif tag is smt.Op.BV_ITE:
            c = _child_bool(ctx, out, node, 0)
            t = _child_bv(ctx, out, node, 1)
            e = _child_bv(ctx, out, node, 2)
            out.bvs[index] = z3.If(c, t, e)
        elif tag is smt.Op.BV_SELECT:
            pairs = node.aux_hi
            result = _child_bv(ctx, out, node, pairs * 2)
            for pair in range(pairs - 1, -1, -1):
                selector = _child_bool(ctx, out, node, pair * 2)
                value = _child_bv(ctx, out, node, pair * 2 + 1)
                result = z3.If(selector, value, result)
            out.bvs[index] = result
        elif tag is smt.Op.BOOL_TRUE:
            out.bools[index] = z3.BoolVal(True, ctx=z3_ctx)
        elif tag is smt.Op.BOOL_FALSE:
            out.bools[index] = z3.BoolVal(False, ctx=z3_ctx)
        elif tag is smt.Op.BOOL_VAR:
            name = _node_blob(ctx, node, "Bool variable").decode("utf-8")
            term = bool_vars.get(name)
            if term is None:
                term = z3.Bool(f"bool_{index}", ctx=z3_ctx)
                bool_vars[name] = term
            out.variables.append(_Z3Variable(_bool_ref(index), smt.Sort.BOOL, 0))
            out.bools[index] = term
        elif tag is smt.Op.BOOL_NOT:
            x = _child_bool(ctx, out, node, 0)
            out.bools[index] = z3.Not(x)
        elif tag is smt.Op.BOOL_AND:
            a, b = _child_bool2(ctx, out, node)
            out.bools[index] = z3.And(a, b)
        elif tag is smt.Op.BOOL_OR:
            a, b = _child_bool2(ctx, out, node)
            out.bools[index] = z3.Or(a, b)
        elif tag is smt.Op.BOOL_IMPLIES:
            a, b = _child_bool2(ctx, out, node)
            out.bools[index] = z3.Implies(a, b)
        elif tag is smt.Op.BV_EQ:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = a == b
        elif tag is smt.Op.BV_ULT:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = z3.ULT(a, b)
        elif tag is smt.Op.BV_ULE:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = z3.ULE(a, b)
        elif tag is smt.Op.BV_SLT:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = a < b
        elif tag is smt.Op.BV_SLE:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = a <= b
        elif tag is smt.Op.UADD_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = z3.ULT(a + b, a)
        elif tag is smt.Op.SADD_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = _signed_add_overflow(a, b, z3)
        elif tag is smt.Op.USUB_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = z3.ULT(a, b)
        elif tag is smt.Op.SSUB_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = _signed_sub_overflow(a, b, z3)
        elif tag is smt.Op.UMUL_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = _unsigned_mul_overflow(a, b, z3)
        elif tag is smt.Op.SMUL_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = _signed_mul_overflow(a, b, z3)
        elif tag is smt.Op.NEG_OVF:
            a = _child_bv(ctx, out, node, 0)
            out.bools[index] = a == _signed_min_bv(a.size(), z3, z3_ctx)
        elif tag is smt.Op.SDIV_OVF:
            a, b = _child_bv2(ctx, out, node)
            out.bools[index] = z3.And(
                a == _signed_min_bv(a.size(), z3, z3_ctx),
                b == _ones_bv(b.size(), z3, z3_ctx),
            )
        else:  # pragma: no cover - Op enum should cover all tags
            raise smt.ProtocolError(f"unsupported operation {tag}")
    return out


def _validate_node_shape(node: smt.Node) -> None:
    tag = node.tag
    result_sort = smt.Sort.BV if tag <= smt.Op.BV_SELECT else smt.Sort.BOOL
    if result_sort is smt.Sort.BOOL and node.width != 0:
        raise smt.ProtocolError(f"Bool node {tag.name} has non-zero width")
    if result_sort is smt.Sort.BV and not 1 <= node.width <= smt.MAX_WIDTH:
        raise smt.ProtocolError(f"BV node {tag.name} has invalid width {node.width}")

    expected: Optional[int]
    if tag in (smt.Op.BV_VAR, smt.Op.BV_CONST, smt.Op.BOOL_TRUE, smt.Op.BOOL_FALSE, smt.Op.BOOL_VAR):
        expected = 0
    elif tag in (
        smt.Op.BV_NOT,
        smt.Op.BV_NEG,
        smt.Op.BV_EXTRACT,
        smt.Op.BV_ZEXT,
        smt.Op.BV_SEXT,
        smt.Op.BOOL_NOT,
        smt.Op.NEG_OVF,
    ):
        expected = 1
    elif tag is smt.Op.BV_ITE:
        expected = 3
    elif tag is smt.Op.BV_SELECT:
        expected = node.aux_hi * 2 + 1
    else:
        expected = 2
    if node.arity != expected:
        raise smt.ProtocolError(
            f"node {tag.name} has arity {node.arity}, expected {expected}"
        )
    if tag is smt.Op.BV_EXTRACT and node.aux_lo > node.aux_hi:
        raise smt.ProtocolError("extract low bit exceeds high bit")


def _child_ref(ctx: smt.Context, node: smt.Node, offset: int) -> int:
    if offset >= node.arity:
        raise smt.ProtocolError(f"child offset {offset} exceeds arity {node.arity}")
    return ctx._children[node.children + offset]


def _child_bv(ctx: smt.Context, translation: _Z3Translation, node: smt.Node, offset: int) -> Any:
    return translation.bv(_child_ref(ctx, node, offset))


def _child_bool(ctx: smt.Context, translation: _Z3Translation, node: smt.Node, offset: int) -> Any:
    return translation.bool(_child_ref(ctx, node, offset))


def _child_bv2(ctx: smt.Context, translation: _Z3Translation, node: smt.Node) -> tuple[Any, Any]:
    return _child_bv(ctx, translation, node, 0), _child_bv(ctx, translation, node, 1)


def _child_bool2(ctx: smt.Context, translation: _Z3Translation, node: smt.Node) -> tuple[Any, Any]:
    return _child_bool(ctx, translation, node, 0), _child_bool(ctx, translation, node, 1)


def _node_blob(ctx: smt.Context, node: smt.Node, context: str) -> bytes:
    offset, length = _blob_ref(node.payload)
    return _blob_bytes(ctx, offset, length, context)


def _z3_bv_const(ctx: smt.Context, node: smt.Node, z3: Any, z3_ctx: Any) -> Any:
    if node.width <= 64:
        mask = (1 << node.width) - 1 if node.width < 64 else (1 << 64) - 1
        value = node.payload & mask
    else:
        data = _node_blob(ctx, node, "wide BV constant")
        expected = _bytes_for_width(node.width)
        if len(data) != expected:
            raise smt.ProtocolError("wide BV constant length does not match width")
        value = int.from_bytes(data, "little")
    return z3.BitVecVal(value, node.width, ctx=z3_ctx)


def _bvsmod(a: Any, b: Any, z3: Any) -> Any:
    ast = z3.Z3_mk_bvsmod(a.ctx_ref(), a.as_ast(), b.as_ast())
    return z3.BitVecRef(ast, a.ctx)


def _sign_bool(value: Any, z3: Any) -> Any:
    return z3.Extract(value.size() - 1, value.size() - 1, value) == z3.BitVecVal(
        1, 1, ctx=value.ctx
    )


def _signed_add_overflow(a: Any, b: Any, z3: Any) -> Any:
    total = a + b
    sa = _sign_bool(a, z3)
    sb = _sign_bool(b, z3)
    st = _sign_bool(total, z3)
    return z3.Or(z3.And(z3.Not(sa), z3.Not(sb), st), z3.And(sa, sb, z3.Not(st)))


def _signed_sub_overflow(a: Any, b: Any, z3: Any) -> Any:
    diff = a - b
    sa = _sign_bool(a, z3)
    sb = _sign_bool(b, z3)
    sd = _sign_bool(diff, z3)
    return z3.Or(z3.And(z3.Not(sa), sb, sd), z3.And(sa, z3.Not(sb), z3.Not(sd)))


def _unsigned_mul_overflow(a: Any, b: Any, z3: Any) -> Any:
    width = a.size()
    product = z3.ZeroExt(width, a) * z3.ZeroExt(width, b)
    high = z3.Extract(width * 2 - 1, width, product)
    return high != z3.BitVecVal(0, width, ctx=a.ctx)


def _signed_mul_overflow(a: Any, b: Any, z3: Any) -> Any:
    width = a.size()
    product = z3.SignExt(width, a) * z3.SignExt(width, b)
    low = z3.Extract(width - 1, 0, product)
    return product != z3.SignExt(width, low)


def _signed_min_bv(width: int, z3: Any, z3_ctx: Any) -> Any:
    return z3.BitVecVal(1 << (width - 1), width, ctx=z3_ctx)


def _ones_bv(width: int, z3: Any, z3_ctx: Any) -> Any:
    return z3.BitVecVal((1 << width) - 1, width, ctx=z3_ctx)


def _check_with_deadline(z3: Any, solver: Any, assumptions: list[Any], deadline: _Deadline) -> Any:
    remaining = deadline.remaining_ms()
    if remaining == 0:
        return z3.unknown
    if remaining is not None:
        solver.set(timeout=remaining)
    return solver.check(*assumptions)


def _unknown_reason(solver: Any) -> str:
    try:
        reason = solver.reason_unknown()
    except Exception:
        reason = ""
    return reason or "z3 returned unknown"


def _build_core(solver: Any, trackers: list[tuple[str, Any]]) -> list[str]:
    core = solver.unsat_core()
    names: list[str] = []
    for name, tracker in trackers:
        if any(tracker.eq(item) for item in core):
            names.append(name)
    return names


def _optimization_prefers_one(*, signed: bool, minimize: bool, sign_bit: bool) -> bool:
    if not signed:
        return not minimize
    if sign_bit:
        return minimize
    return not minimize


def _set_bit(data: bytearray, bit: int) -> None:
    data[bit // 8] |= 1 << (bit % 8)


def _encode_model(translation: _Z3Translation, model: Any) -> bytes:
    entries = bytearray(struct.pack("<I", len(translation.variables)))
    for variable in translation.variables:
        entries.extend(struct.pack("<I", variable.node_ref))
        if variable.sort is smt.Sort.BOOL:
            value = model.eval(translation.bool(variable.node_ref), model_completion=True)
            entries.extend(_encode_scalar_bool(_z3_bool_value(value)))
        else:
            value = model.eval(translation.bv(variable.node_ref), model_completion=True)
            entries.extend(_encode_scalar_bv(variable.width, _z3_bv_value_bytes(value, variable.width)))
    return bytes(entries)


def _z3_bool_value(value: Any) -> bool:
    if value.ctx is not None:
        # z3.is_true is module-level, but BoolRef values expose eq reliably.
        return bool(value)
    return bool(value)


def _z3_bv_value_bytes(value: Any, width: int) -> bytes:
    raw = int(value.as_long()) & ((1 << width) - 1)
    data = bytearray(raw.to_bytes(_bytes_for_width(width), "little"))
    valid = width % 8
    if valid:
        data[-1] &= (1 << valid) - 1
    return bytes(data)


def _encode_scalar_bool(value: bool) -> bytes:
    return struct.pack("<II", 0, 1) + (b"\x01" if value else b"\x00")


def _encode_scalar_bv(width: int, data: bytes) -> bytes:
    expected = _bytes_for_width(width)
    if len(data) != expected:
        raise smt.ProtocolError("BV scalar length does not match width")
    return struct.pack("<II", width, len(data)) + data


def _encode_core(names: list[str]) -> bytes:
    payload = bytearray(struct.pack("<I", len(names)))
    for name in names:
        data = name.encode("utf-8")
        payload.extend(struct.pack("<I", len(data)))
        payload.extend(data)
    return bytes(payload)


def _simplify_response(request: _BinaryRequest) -> bytes:
    payload = (
        struct.pack("<II", len(request.expression), request.target_node)
        + request.expression
    )
    return _response(request.request_id, smt.Status.SIMPLIFIED, RESP_HAS_EXPR, payload)


def _unknown_response(request_id: int, message: str) -> bytes:
    if message:
        return _response(
            request_id,
            smt.Status.UNKNOWN,
            RESP_HAS_MESSAGE,
            message.encode("utf-8"),
        )
    return _response(request_id, smt.Status.UNKNOWN, 0, b"")


def _error_response(request_id: int, message: str) -> bytes:
    return _response(
        request_id,
        smt.Status.ERROR,
        RESP_HAS_MESSAGE,
        message.encode("utf-8", "replace"),
    )


def _response(request_id: int, status: smt.Status, flags: int, payload: bytes) -> bytes:
    if len(payload) > 0xFFFFFFFF:
        raise smt.ProtocolError("response payload too large")
    return (
        smt.RESPONSE_MAGIC
        + struct.pack("<I", request_id)
        + bytes([int(status), flags])
        + struct.pack("<I", len(payload))
        + b"\x00\x00"
        + payload
    )


def _frame(payload: bytes) -> bytes:
    if len(payload) > 0xFFFFFFFF:
        raise smt.ProtocolError("frame payload too large")
    return struct.pack("<I", len(payload)) + payload


def _text_error(message: str) -> bytes:
    quoted = message.replace('"', '""')
    return f'(error "{quoted}")\n'.encode("utf-8")


def _recv_exact_or_none(sock: socket.socket, length: int) -> Optional[bytes]:
    data = bytearray()
    while len(data) < length:
        chunk = sock.recv(length - len(data))
        if not chunk:
            if data:
                raise EOFError("socket closed while reading frame")
            return None
        data.extend(chunk)
    return bytes(data)


def _recv_exact(sock: socket.socket, length: int) -> bytes:
    data = _recv_exact_or_none(sock, length)
    if data is None:
        raise EOFError("socket closed while reading frame")
    return data


def _safe_send(sock: socket.socket, data: bytes) -> None:
    try:
        sock.sendall(data)
    except OSError:
        pass


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Run the experimental Python Z3 SMT server")
    parser.add_argument("--host", default=smt.DEFAULT_SERVER_HOST)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--max-frame-bytes", type=int, default=DEFAULT_MAX_FRAME_BYTES)
    parser.add_argument("--max-response-bytes", type=int, default=DEFAULT_MAX_RESPONSE_BYTES)
    args = parser.parse_args(argv)

    with Z3Server.start(
        args.host,
        args.port,
        max_frame_bytes=args.max_frame_bytes,
        max_response_bytes=args.max_response_bytes,
    ) as server:
        print(server.server_address, flush=True)
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())


__all__ = [
    "Z3Server",
    "start_z3_server",
    "DEFAULT_MAX_FRAME_BYTES",
    "DEFAULT_MAX_RESPONSE_BYTES",
    "DEFAULT_MAX_CONNECTIONS",
    "main",
]
