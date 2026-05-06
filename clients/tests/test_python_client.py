import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))

import smt_wire as smt


def hex_bytes(s: str) -> bytes:
    return bytes.fromhex("".join(s.split()))


def test_python_client_matches_simple_sat_golden_vector():
    b = smt.Builder()
    x = b.bv_var("x", 8)
    one = b.bv_const(1, 8)
    b.assert_(b.bv_eq(x, one))
    assert b.build_solve_request(0x01020304, 500, True, False) == hex_bytes(
        "53 4d 54 51 04 03 02 01 00 01 f4 01 00 00 71 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "53 4d 54 00 01 00 00 00 03 00 00 00 02 00 00 00 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "00 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00"
        "01 00 00 00 08 00 00 00 00 00 00 00 00 00 00 00 01 00 00 00 00 00 00 00"
        "1f 02 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
        "00 00 00 00 01 00 00 00 78 02 00 00 80"
    )


def test_python_client_validates_width_and_sort():
    b = smt.Builder()
    a = b.bv_var("a", 8)
    c = b.bv_var("c", 16)
    p = b.bool_var("p")
    rotated = b.bv_rotate_left(a, 3)
    assert smt.is_bv_ref(rotated)
    assert b.build_minimize_request(3, a, signed=True, want_model=True).startswith(b"SMTQ")
    try:
        b.bv_add(a, c)
        raise AssertionError("expected width error")
    except ValueError:
        pass
    try:
        b.bool_and(p, a)
        raise AssertionError("expected sort error")
    except ValueError:
        pass


def test_python_wide_integer_constant_uses_blob_encoding_and_masks_to_width():
    b = smt.Builder()
    b.bv_const((1 << 80) | (1 << 64) | 3, 65)
    expr = b.to_bytes()
    assert int.from_bytes(expr[16:20], "little") == 9  # blob_len
    assert int.from_bytes(expr[48:56], "little") == 9  # payload = blob ref (offset 0, len 9)
    assert expr[-1] == 1  # only the 65th bit may remain in the final byte


def test_python_response_parser():
    response = b"SMTR" + (7).to_bytes(4, "little") + bytes([smt.ERROR, smt.HAS_MESSAGE]) + (3).to_bytes(4, "little") + b"\0\0bad"
    parsed = smt.parse_response(response)
    assert parsed.request_id == 7
    assert parsed.status == smt.ERROR
    assert parsed.payload == b"bad"
    assert parsed.message() == "bad"

    scalar = (8).to_bytes(4, "little") + (1).to_bytes(4, "little") + b"*"
    model_payload = (1).to_bytes(4, "little") + (0).to_bytes(4, "little") + scalar
    model_response = smt.parse_response(b"SMTR" + (8).to_bytes(4, "little") + bytes([smt.SAT, smt.HAS_MODEL]) + len(model_payload).to_bytes(4, "little") + b"\0\0" + model_payload)
    model = model_response.model()
    assert model[0].node_ref == 0
    assert model[0].value.width == 8
    assert model[0].value.as_int() == 42

    core_payload = (1).to_bytes(4, "little") + (2).to_bytes(4, "little") + b"a0"
    assert smt.parse_core(core_payload) == ["a0"]


def test_python_response_parser_rejects_bad_status_flag_combinations():
    bad_error = b"SMTR" + (1).to_bytes(4, "little") + bytes([smt.ERROR, 0]) + (0).to_bytes(4, "little") + b"\0\0"
    try:
        smt.parse_response(bad_error)
        raise AssertionError("expected bad ERROR response to be rejected")
    except ValueError:
        pass

    bad_sat = b"SMTR" + (1).to_bytes(4, "little") + bytes([smt.SAT, smt.HAS_CORE]) + (0).to_bytes(4, "little") + b"\0\0"
    try:
        smt.parse_response(bad_sat)
        raise AssertionError("expected bad SAT flags to be rejected")
    except ValueError:
        pass


def test_python_tcp_client_rejects_oversized_response_before_allocation():
    class FakeSocket:
        def __init__(self) -> None:
            self.sent = bytearray()
            self.incoming = bytearray((1024).to_bytes(4, "little"))

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

    client = smt.TcpClient.from_socket(FakeSocket())
    client.set_max_response_bytes(8)
    try:
        client.send_payload(b"x")
        raise AssertionError("expected oversized response frame to be rejected")
    except ValueError:
        pass


if __name__ == "__main__":
    test_python_client_matches_simple_sat_golden_vector()
    test_python_client_validates_width_and_sort()
    test_python_wide_integer_constant_uses_blob_encoding_and_masks_to_width()
    test_python_response_parser()
    test_python_response_parser_rejects_bad_status_flag_combinations()
    test_python_tcp_client_rejects_oversized_response_before_allocation()
