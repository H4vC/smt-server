# Shared SMT-LIB frontend

SMT-LIB parsing lives in `crates/smt-qfbv-smtlib`. It is intentionally solver-agnostic: the crate parses one script with `yaspar`, normalizes common QF_BV/Bool constructs, and lowers through the `QfBvSink` trait. The same parser is used by:

- `crates/smt-server/src/smtlib.rs`, where `WireSmtLibSink` builds an `smt-wire` request;
- `crates/qfbvsmtrs/src/frontend.rs`, where `QfbvSmtLibSink` builds qfbvsmtrs IR.

This avoids keeping separate SMT-LIB parsers in sync.

## Frontend policies

`FrontendOptions` controls the policy differences between server text mode and standalone qfbvsmtrs:

| Option set | Logic policy | `push`/`pop` | Typical use |
|---|---|---|---|
| `FrontendOptions::server_text()` | accepts `QF_BV` | rejects incremental commands | `smt-server` text frames lowered to one stateless wire request |
| `FrontendOptions::standalone()` | accepts `QF_BV` or `ALL` | simulates scopes in the sink | qfbvsmtrs CLI/API |

Both modes require a `check-sat` command before response-oriented commands are considered complete.

## Supported commands

The shared frontend supports the QF_BV/Bool commands used by the project tests and corpus runner:

- `set-logic` (`QF_BV`; standalone also accepts `ALL`);
- no-op metadata/options: `set-option`, `set-info`, `echo`, `exit`;
- `declare-const` and 0-arity `declare-fun`;
- `define-const` and non-recursive `define-fun` macros;
- `assert`, including `(! term :named name)`;
- `check-sat` and `check-sat-assuming`;
- `get-model`, `get-value`, and `get-unsat-core`;
- `push`/`pop` only when the selected frontend policy allows simulated scopes.

Unsupported stateful commands such as `reset` and `reset-assertions` are rejected.

`get-value` currently accepts declared symbols. The frontend adds those symbols to the requested model/value set so formatters can emit their values when the backend returns a model.

## Supported terms

Supported Bool constructs:

- `true`, `false`;
- `not`, `and`, `or`, `=>`, `xor`;
- n-ary `=` and `distinct`;
- `ite` over Bool or BV terms;
- `let` bindings;
- non-named annotations where the base term is still a supported term.

Supported bit-vector constructs:

- literals: `#b...`, `#x...`, and indexed literals such as `(_ bv42 8)`;
- bitwise/arithmetic: `bvnot`, `bvneg`, `bvand`, `bvnand`, `bvor`, `bvnor`, `bvxor`, `bvxnor`, `bvadd`, `bvsub`, `bvmul`;
- division/remainder: `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`;
- shifts: `bvshl`, `bvlshr`, `bvashr`;
- comparisons: `bvult`, `bvule`, `bvugt`, `bvuge`, `bvslt`, `bvsle`, `bvsgt`, `bvsge`;
- structural ops: `concat`, `((_ extract hi lo) x)`, `((_ zero_extend n) x)`, `((_ sign_extend n) x)`, `((_ repeat n) x)`, `((_ rotate_left n) x)`, `((_ rotate_right n) x)`;
- `bvcomp`;
- overflow predicates accepted by this project: `bvuaddo`/`uaddo`, `bvsaddo`/`saddo`, `bvusubo`/`usubo`, `bvssubo`/`ssubo`, `bvumulo`/`umulo`, `bvsmulo`/`smulo`, `bvnego`/`nego`, `bvsdivo`/`sdivo`.

The frontend is limited to QF_BV/Bool. Arrays, floating point, quantifiers, uninterpreted functions, recursive definitions, and non-zero-arity declarations are outside the current contract.

## Server text behavior

Server text frames are still stateless. The server reads exactly one length-prefixed script and returns one SMT-LIB text response. In server text mode:

1. `smt-qfbv-smtlib` tries to lower the script into an `smt-wire` `SOLVE` request.
2. The selected backend handles that request and returns a `QueryResult`.
3. `smt-server` formats `sat`/`unsat`/`unknown`, plus `(model ...)`, `get-value`, or unsat-core output when requested.

When the selected backend supports qfbvsmtrs text fallback and the server wire-lowering frontend rejects a script, the server can invoke qfbvsmtrs' standalone parser/solver on a worker thread. The fallback uses a default 30s budget, overrideable with `SMT_SERVER_TEXT_QFBVSMTRS_BUDGET_MS`; a nonzero fallback budget selects qfbvsmtrs' polling DPLL backend to avoid in-process timeout overruns.

## Error model

Frontend errors are categorized as parse errors, unsupported constructs, invalid typed terms, or sink errors. Server text mode returns SMT-LIB-style `(error "...")` output rather than panicking. Binary clients receive normal binary `ERROR` responses when a text-derived wire request cannot be constructed or validated.
