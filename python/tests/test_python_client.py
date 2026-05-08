import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import smt_wire as smt


def hex_bytes(s: str) -> bytes:
    return bytes.fromhex("".join(s.split()))


def test_python_client_matches_simple_sat_golden_vector():
    ctx = smt.Context()
    x = ctx.bv_var("x", 8)
    one = ctx.bv_const(1, 8)
    ctx.assert_(ctx.bv_eq(x, one))
    assert ctx._build_solve_request(0x01020304, 500, True, False).payload == hex_bytes(
        "53 4d 54 51 04 03 02 01 00 01 f4 01 00 00 71 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "53 4d 54 00 01 00 00 00 03 00 00 00 02 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00"
        "01 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00"
        "1f 02 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "00 00 00 00 01 00 00 00 78 02 00 00 80"
    )


def test_context_ids_and_repr_are_debug_friendly():
    a = smt.Context()
    b = smt.Context()
    assert b.id == a.id + 1
    assert str(a) == f"Context#{a.id}"
    assert repr(a).startswith(f"Context#{a.id}(nodes=0, assertions=0)")


def test_int_enums_print_symbolically():
    assert str(smt.Status.SAT) == "Status.SAT"
    assert f"{smt.Status.SIMPLIFIED}" == "Status.SIMPLIFIED"
    assert str(smt.Op.BV_ADD) == "Op.BV_ADD"
    assert str(smt.Command.SOLVE) == "Command.SOLVE"
    assert str(smt.ResponseFlag.HAS_MODEL) == "ResponseFlag.HAS_MODEL"
    assert str(smt.ResponseFlag.HAS_MODEL | smt.ResponseFlag.HAS_VALUE) == "ResponseFlag.HAS_MODEL|HAS_VALUE"


def test_terms_use_handle_equality_and_hashing():
    ctx = smt.Context()
    x = ctx.bv_var("x", 8)
    assert x == ctx.bv_var("x", 8)
    assert x != smt.Context().bv_var("x", 8)
    assert {x, ctx.bv_var("x", 8)} == {x}


def test_terms_validate_width_sort_and_context():
    ctx = smt.Context()
    a = ctx.bv_var("a", 8)
    c = ctx.bv_var("c", 16)
    assert ctx.bv_var("a", 8) is a
    try:
        ctx.bv_var("a", 16)
        raise AssertionError("expected symbol width error")
    except smt.SortError:
        pass
    try:
        ctx.bool_var("a")
        raise AssertionError("expected symbol sort error")
    except smt.SortError:
        pass
    p = ctx.bool_var("p")
    assert ctx.bool_var("p") is p
    assert not hasattr(a, "add")
    assert not hasattr(p, "and_")
    rotated = ctx.bv_rotate_left(a, 3)
    assert isinstance(rotated, smt.BVTerm)
    assert ctx._build_minimize_request(3, a, signed=True, want_model=True).payload.startswith(b"SMTQ")
    try:
        a + c
        raise AssertionError("expected width error")
    except smt.WidthMismatchError:
        pass
    assert isinstance(a + 1, smt.BVTerm)
    assert isinstance(0xFF & a, smt.BVTerm)
    try:
        a + True  # type: ignore[operator]
        raise AssertionError("expected bool coercion error")
    except smt.SortError:
        pass
    try:
        True + a  # type: ignore[operator]
        raise AssertionError("expected bool coercion error")
    except smt.SortError:
        pass
    try:
        ctx.bool_and(p, a)  # type: ignore[arg-type]
        raise AssertionError("expected sort error")
    except smt.SortError:
        pass
    other = smt.Context().bv_var("other", 8)
    try:
        a + other
        raise AssertionError("expected context error")
    except smt.ContextMismatchError:
        pass


def test_to_smt2_depth_limited_rendering():
    ctx = smt.Context()
    x = ctx.bv_var("x", 32)
    y = ctx.bv_var("y", 32)
    mba = (x ^ y) + (ctx.bv_const(2, 32) * (x & y))
    assert str(mba) == "(bvadd |#2| |#5|) ; #6"
    assert mba.to_smt2(depth=1) == "(bvadd (bvxor x y) (bvmul #x00000002 |#4|)) ; #6"
    assert mba.to_smt2(depth=-1) == "(bvadd (bvxor x y) (bvmul #x00000002 (bvand x y))) ; #6"
    try:
        mba.to_smt2(depth=-2)
        raise AssertionError("expected invalid depth")
    except ValueError:
        pass


def test_context_to_smt2_renders_self_contained_script():
    ctx = smt.Context()
    x = ctx.bv_var("x y", 8)
    p = ctx.bool_var("p")
    named = ctx.bool_or(p, ctx.bv_eq(x, 42))
    assumption = ctx.bv_ult(x, 100)
    ctx.assert_named("named weird", named)
    ctx.assume(assumption)
    assert ctx.assertions == [named]
    assert ctx.named_assertions == [("named weird", named)]
    assert ctx.assumptions == [assumption]
    assert ctx.to_smt2(get_model=True) == (
        "(set-logic QF_BV)\n"
        "(set-option :produce-models true)\n"
        "(declare-const |x y| (_ BitVec 8))\n"
        "(declare-const p Bool)\n"
        "(assert (! (or p (= |x y| #x2a)) :named |named weird|)) ; #4\n"
        "(assert (bvult |x y| #x64)) ; assumption #6\n"
        "(check-sat)\n"
        "(get-model)\n"
    )


def test_to_smt2_quotes_symbols_and_formats_non_nibble_constants():
    ctx = smt.Context()
    weird = ctx.bv_var("x y", 3)
    expr = weird + 5
    assert expr.to_smt2(depth=-1) == "(bvadd |x y| #b101) ; #2"


def test_to_smt2_renders_parameterized_bv_ops():
    ctx = smt.Context()
    x = ctx.bv_var("x", 16)
    low = ctx.bv_extract(x, 7, 0)
    assert low.to_smt2(depth=-1) == "((_ extract 7 0) x) ; #1"
    assert ctx.bv_zext(low, 8).to_smt2(depth=-1) == "((_ zero_extend 8) ((_ extract 7 0) x)) ; #2"
    assert ctx.bv_sext(low, 8).to_smt2(depth=-1) == "((_ sign_extend 8) ((_ extract 7 0) x)) ; #3"
    assert ctx.bv_select([], [], x).to_smt2(depth=-1) == "x ; #4"


def test_python_ints_are_coerced_to_bv_constants():
    ctx = smt.Context()
    x = ctx.bv_var("x", 8)
    expr = (0xFF & x) + 3
    assert expr.to_smt2(depth=-1) == "(bvadd (bvand x #xff) #x03) ; #4"
    assert (10 - x).to_smt2(depth=-1) == "(bvsub #x0a x) ; #6"
    assert (1 << x).to_smt2(depth=-1) == "(bvshl #x01 x) ; #8"


def test_term_visit_lowers_result_dag_shape():
    ctx = smt.Context()
    x = ctx.bv_var("x", 8)
    sub = x + 1
    expr = sub * sub
    assert int(smt.Op.BV_ADD) == 7
    assert smt.Op.BV_ADD.symbol == "bvadd"
    assert [term.op for term in expr.walk()] == [smt.Op.BV_VAR, smt.Op.BV_CONST, smt.Op.BV_ADD, smt.Op.BV_MUL]

    def lower(term, args):
        if term.op is smt.Op.BV_VAR:
            return f"var({term.name}:{term.width})"
        if term.op is smt.Op.BV_CONST:
            return f"const({term.value}:{term.width})"
        if term.op is smt.Op.BV_ADD:
            return f"add({args[0]}, {args[1]})"
        if term.op is smt.Op.BV_MUL:
            return f"mul({args[0]}, {args[1]})"
        raise AssertionError(term.op)

    assert expr.visit(lower) == "mul(add(var(x:8), const(1:8)), add(var(x:8), const(1:8)))"
    assert ctx.bv_neg_overflows(x).to_smt2(depth=-1) == "(bvnego x) ; #4"


def test_python_wide_integer_constant_uses_blob_encoding_and_masks_to_width():
    ctx = smt.Context()
    ctx.bv_const((1 << 80) | (1 << 64) | 3, 65)
    expr = ctx._expr_bytes(ctx._nodes, ctx._children, ctx._blob)
    assert int.from_bytes(expr[16:20], "little") == 9  # blob_len
    assert int.from_bytes(expr[48:56], "little") == 9  # payload = blob ref (offset 0, len 9)
    assert expr[-1] == 1  # only the 65th bit may remain in the final byte


def test_python_response_parser_and_model_mapping():
    response = b"SMTR" + (7).to_bytes(4, "little") + bytes([smt.Status.ERROR, 16]) + (3).to_bytes(4, "little") + b"\0\0bad"
    parsed = smt._parse_response(response)
    assert parsed.request_id == 7
    assert parsed.status is smt.Status.ERROR
    assert parsed.payload == b"bad"
    assert parsed.message() == "bad"

    ctx = smt.Context()
    x = ctx.bv_var("x", 8)
    ctx.assert_(ctx.bv_eq(x, 42))
    request = ctx._build_solve_request(8)
    compacted_x = request.old_to_new[x.id]
    scalar = (8).to_bytes(4, "little") + (1).to_bytes(4, "little") + b"*"
    model_payload = (1).to_bytes(4, "little") + compacted_x.to_bytes(4, "little") + scalar
    raw = smt._parse_response(b"SMTR" + (8).to_bytes(4, "little") + bytes([smt.Status.SAT, 1]) + len(model_payload).to_bytes(4, "little") + b"\0\0" + model_payload)
    client = smt.Client.from_socket(_FakeSocket.empty())
    model = client._solve_response(raw, request).model
    assert model is not None
    assert model[x].width == 8
    assert model[x].as_int() == 42
    assert int(model[x]) == 42
    assert hex(model[x]) == "0x2a"

    core_payload = (1).to_bytes(4, "little") + (2).to_bytes(4, "little") + b"a0"
    assert smt._parse_core(core_payload) == ["a0"]


def test_python_response_parser_rejects_bad_status_flag_combinations():
    bad_error = b"SMTR" + (1).to_bytes(4, "little") + bytes([smt.Status.ERROR, 0]) + (0).to_bytes(4, "little") + b"\0\0"
    try:
        smt._parse_response(bad_error)
        raise AssertionError("expected bad ERROR response to be rejected")
    except smt.ProtocolError:
        pass

    bad_sat = b"SMTR" + (1).to_bytes(4, "little") + bytes([smt.Status.SAT, 2]) + (0).to_bytes(4, "little") + b"\0\0"
    try:
        smt._parse_response(bad_sat)
        raise AssertionError("expected bad SAT flags to be rejected")
    except smt.ProtocolError:
        pass

    bad_simplified = b"SMTR" + (1).to_bytes(4, "little") + bytes([smt.Status.SIMPLIFIED, 0]) + (0).to_bytes(4, "little") + b"\0\0"
    try:
        smt._parse_response(bad_simplified)
        raise AssertionError("expected bad SIMPLIFIED flags to be rejected")
    except smt.ProtocolError:
        pass


class _FakeSocket:
    def __init__(self, incoming: bytes = b"") -> None:
        self.sent = bytearray()
        self.incoming = bytearray(incoming)

    @classmethod
    def empty(cls):
        return cls()

    def sendall(self, data: bytes) -> None:
        self.sent.extend(data)

    def recv(self, length: int) -> bytes:
        if not self.incoming:
            return b""
        out = self.incoming[:length]
        del self.incoming[:length]
        return bytes(out)

    def close(self) -> None:
        pass

    def settimeout(self, timeout):
        pass


def test_python_client_rejects_oversized_response_before_allocation():
    client = smt.Client.from_socket(_FakeSocket((1024).to_bytes(4, "little")))
    client.set_max_response_bytes(8)
    try:
        client._send_payload(b"x")
        raise AssertionError("expected oversized response frame to be rejected")
    except smt.ProtocolError:
        pass



if __name__ == "__main__":
    test_python_client_matches_simple_sat_golden_vector()
    test_context_ids_and_repr_are_debug_friendly()
    test_int_enums_print_symbolically()
    test_terms_use_handle_equality_and_hashing()
    test_terms_validate_width_sort_and_context()
    test_to_smt2_depth_limited_rendering()
    test_context_to_smt2_renders_self_contained_script()
    test_to_smt2_quotes_symbols_and_formats_non_nibble_constants()
    test_to_smt2_renders_parameterized_bv_ops()
    test_python_ints_are_coerced_to_bv_constants()
    test_term_visit_lowers_result_dag_shape()
    test_python_wide_integer_constant_uses_blob_encoding_and_masks_to_width()
    test_python_response_parser_and_model_mapping()
    test_python_response_parser_rejects_bad_status_flag_combinations()
    test_python_client_rejects_oversized_response_before_allocation()
