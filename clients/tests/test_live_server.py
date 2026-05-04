"""Live end-to-end tests against the smt-server binary.

This intentionally uses only the standard library plus the local Python client
module so it can run directly in CI without pytest.
"""
from __future__ import annotations

import os
import pathlib
import shutil
import socket
import subprocess
import sys
import time
from typing import Iterable

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
CLIENT_ROOT = REPO_ROOT / "clients" / "python"
sys.path.insert(0, str(CLIENT_ROOT))

import smt_wire as smt  # noqa: E402


def unused_local_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def server_binary() -> pathlib.Path:
    subprocess.check_call(["cargo", "build", "-p", "smt-server"], cwd=REPO_ROOT)
    exe = "smt-server.exe" if os.name == "nt" else "smt-server"
    return REPO_ROOT / "target" / "debug" / exe


def server_environment() -> dict[str, str]:
    env = os.environ.copy()
    build_dir = REPO_ROOT / "target" / "debug" / "build"
    z3_dirs = [
        str(path)
        for pattern in ("z3-sys-*/out/z3-*/bin", "z3-sys-*/out/z3-*/lib")
        for path in build_dir.glob(pattern)
    ]
    if z3_dirs:
        sep = os.pathsep
        env["PATH"] = sep.join(z3_dirs + [env.get("PATH", "")])
        env["LD_LIBRARY_PATH"] = sep.join(z3_dirs + [env.get("LD_LIBRARY_PATH", "")])
        env["DYLD_LIBRARY_PATH"] = sep.join(z3_dirs + [env.get("DYLD_LIBRARY_PATH", "")])
    return env


class LiveServer:
    def __init__(self) -> None:
        self.port = unused_local_port()
        self.proc: subprocess.Popen[bytes] | None = None

    def __enter__(self) -> "LiveServer":
        self.proc = subprocess.Popen(
            [str(server_binary()), f"127.0.0.1:{self.port}"],
            cwd=REPO_ROOT,
            env=server_environment(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
        )
        deadline = time.time() + 10.0
        last_error: OSError | None = None
        while time.time() < deadline:
            if self.proc.poll() is not None:
                stderr = self.proc.stderr.read().decode("utf-8", "replace") if self.proc.stderr else ""
                raise RuntimeError(f"smt-server exited early with {self.proc.returncode}: {stderr}")
            try:
                with socket.create_connection(("127.0.0.1", self.port), timeout=0.2):
                    return self
            except OSError as exc:
                last_error = exc
                time.sleep(0.05)
        raise TimeoutError(f"smt-server did not listen on port {self.port}: {last_error}")

    def __exit__(self, *exc_info: object) -> None:
        if self.proc is None:
            return
        self.proc.terminate()
        try:
            self.proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)


def cpp_compiler() -> str | None:
    configured = os.environ.get("CXX")
    if configured and shutil.which(configured):
        return configured
    for candidate in ("clang++", "g++", "c++"):
        found = shutil.which(candidate)
        if found:
            return found
    return None


def test_cpp_client_live_round_trip(port: int) -> None:
    compiler = cpp_compiler()
    if compiler is None:
        print("No C++ compiler available; skipping live C++ client test")
        return
    exe = REPO_ROOT / "target" / ("cpp_live_client.exe" if os.name == "nt" else "cpp_live_client")
    cmd = [
        compiler,
        "-std=c++17",
        "-Wall",
        "-Wextra",
        "-Werror",
        str(REPO_ROOT / "clients" / "tests" / "cpp_live_client.cpp"),
        "-o",
        str(exe),
    ]
    if os.name == "nt":
        cmd.append("-lws2_32")
    subprocess.check_call(cmd, cwd=REPO_ROOT)
    subprocess.check_call([str(exe), "127.0.0.1", str(port)], cwd=REPO_ROOT)


def assert_model_has_value(entries: Iterable[smt.ModelEntry], width: int, value: int) -> None:
    for entry in entries:
        if entry.value.width == width and entry.value.as_int() == value:
            return
    raise AssertionError(f"model does not contain {width}-bit value {value}")


def test_python_client_binary_round_trip(client: smt.TcpClient) -> None:
    builder = smt.Builder()
    x = builder.bv_var("x", 4)
    builder.assert_(builder.bv_eq(x, builder.bv_const(2, 4)))

    response = client.send_request(builder.build_solve_request(0x1001, want_model=True))
    assert response.request_id == 0x1001
    assert response.status == smt.SAT
    assert response.flags == smt.HAS_MODEL
    assert_model_has_value(response.model(), 4, 2)


def test_binary_cache_rebinds_response_ids(client: smt.TcpClient) -> None:
    builder = smt.Builder()
    x = builder.bv_var("cached", 3)
    builder.assert_(builder.bv_eq(x, builder.bv_const(5, 3)))

    first = client.send_request(builder.build_solve_request(0x2001))
    second = client.send_request(builder.build_solve_request(0x2002))
    assert first.request_id == 0x2001
    assert second.request_id == 0x2002
    assert first.status == smt.SAT
    assert second.status == smt.SAT


def test_python_client_optimization_round_trip(client: smt.TcpClient) -> None:
    builder = smt.Builder()
    x = builder.bv_var("opt", 4)
    builder.assert_(builder.bv_uge(x, builder.bv_const(5, 4)))

    response = client.send_request(builder.build_minimize_request(0x3001, x))
    assert response.request_id == 0x3001
    assert response.status == smt.SAT
    assert response.flags == smt.HAS_VALUE
    optimum = response.optimization().optimum
    assert optimum.width == 4
    assert optimum.as_int() == 5


def test_text_smtlib_round_trip(client: smt.TcpClient) -> None:
    script = b"""
        #| yaspar parses this block comment in the live text path |#
        (set-logic QF_BV)
        (declare-const |x y| (_ BitVec 2))
        (assert (= |x y| #b11))
        (check-sat)
        (get-value (|x y|))
    """
    text = client.send_text(script)
    assert text.startswith("sat\n"), text
    assert "(|x y| #b11)" in text, text


def main() -> None:
    with LiveServer() as server:
        with smt.TcpClient("127.0.0.1", server.port, timeout=5) as client:
            test_python_client_binary_round_trip(client)
            test_binary_cache_rebinds_response_ids(client)
            test_python_client_optimization_round_trip(client)
            test_text_smtlib_round_trip(client)
        test_cpp_client_live_round_trip(server.port)


if __name__ == "__main__":
    main()
