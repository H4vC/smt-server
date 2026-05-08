import smt_wire as smt


ctx = smt.Context()
print(ctx)  # Context#1, Context#2, ...

x = ctx.bv_var("x", 32)
y = ctx.bv_var("y", 32)

# Terms are thin handles. Arithmetic/bitwise dunders forward to Context methods,
# and Python ints are coerced to BV constants using the left term's width.
x_plus_y = x + y
mba = (x ^ y) + ((x & y) * 2)
masked = 0xFF & (x + 3)

# Named operations live on Context: comparisons, structural operations, and Bool ops.
identity_holds = ctx.bv_eq(mba, x_plus_y)
low_x_is_42 = ctx.bv_eq(ctx.bv_extract(x, 7, 0), 42)
ctx.assert_(ctx.bool_and(identity_holds, low_x_is_42))

# __str__ renders one layer by default. With to_smt2 you get full depth
print("MBA:", mba)
print("MBA full:", mba.to_smt2())
print("masked:", masked.to_smt2())


# A visitor can lower a returned/simplified DAG into your own IR. This one
# prints a small reverse Polish notation string for the MBA expression.
def to_rpn(term: smt.Term, args: tuple[str, ...]) -> str:
    if term.op is smt.Op.BV_VAR:
        return term.name
    if term.op is smt.Op.BV_CONST:
        assert isinstance(term, smt.BVTerm)
        return f"{term.value}:{term.width}"
    return " ".join((*args, term.op.symbol))


print("RPN:", mba.visit(to_rpn))

# Start the server first:
#   cargo run -p smt-server -- 127.0.0.1:9123
with smt.Client() as client:
    resp = client.solve(ctx)
    print(resp.status)
    if resp.status is smt.Status.SAT and resp.model is not None:
        for var, value in resp.model.items():
            print(f"{var.name} = {hex(int(value))}")

    simplified = client.simplify(mba)
    if simplified.term is not None:
        print("simplified MBA:", simplified.term.to_smt2(depth=-1))

# Dump a full SMT-LIB script for debugging or for feeding to solvers like Z3.
print("\nSMT-LIB:")
ctx_smt2 = ctx.to_smt2()
print(ctx_smt2)

with smt.Client() as client:
    smt_resp = client.smt2(ctx_smt2)
    print(smt_resp)