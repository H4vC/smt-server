# smt-wire Python client

Typed dependency-free Python client for the SMT v1 wire protocol.

`Client()` connects to `SMT_SERVER_ADDRESS=<host>:<port>` when set, otherwise `127.0.0.1:9123`.

Install from this repository with pip using the Python subdirectory:

```sh
pip install 'git+https://github.com/LLVMParty/smt-server.git#subdirectory=python'
```

For local development from the repository root:

```sh
python3 python/tests/test_python_client.py
```
