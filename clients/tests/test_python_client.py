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


def test_python_response_parser():
    response = b"SMTR" + (7).to_bytes(4, "little") + bytes([smt.ERROR, smt.HAS_MESSAGE]) + (3).to_bytes(4, "little") + b"\0\0bad"
    parsed = smt.parse_response(response)
    assert parsed.request_id == 7
    assert parsed.status == smt.ERROR
    assert parsed.payload == b"bad"


if __name__ == "__main__":
    test_python_client_matches_simple_sat_golden_vector()
    test_python_client_validates_width_and_sort()
    test_python_response_parser()
