# smt-wire Python client

Typed dependency-free Python client for the SMT v1 wire protocol. The optional `smt_z3_server` module provides an in-process Z3-backed TCP server for experiments.

`Client()` connects to `SMT_SERVER_ADDRESS=<host>:<port>` when set, otherwise `127.0.0.1:9123`.

Install from this repository with pip using the Python subdirectory:

```sh
pip install 'git+https://github.com/LLVMParty/smt-server.git#subdirectory=python'
```

Install the optional Z3 server dependency from the Python subdirectory:

```sh
pip install -e 'python[z3]'
```

Start a random-port in-process server from Python:

```python
import smt_wire as smt
from smt_z3_server import Z3Server

with Z3Server.start(port=0) as server:
    with smt.Client(server.host, server.port) as client:
        # use the existing client API
        pass
```

Or run it as a module; it prints the selected address after binding:

```sh
python -m smt_z3_server --port 0
```

For local development from the repository root:

```sh
python3 python/tests/test_python_client.py
python3 python/tests/test_z3_server.py
```
