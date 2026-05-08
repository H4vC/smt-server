#include <smt_wire/smt_wire.hpp>
#include <cassert>
#include <cstdint>
#include <vector>

int main() {
    smt_wire::Context ctx;
    auto x = ctx.bv_var("x", 8);
    assert(ctx.bv_var("x", 8) == x.as_term());
    bool bad_symbol_threw = false;
    try { (void)ctx.bv_var("x", 16); } catch (const std::invalid_argument&) { bad_symbol_threw = true; }
    assert(bad_symbol_threw);
    bad_symbol_threw = false;
    try { (void)ctx.bool_var("x"); } catch (const std::invalid_argument&) { bad_symbol_threw = true; }
    assert(bad_symbol_threw);

    auto expr = (x + 1u) * (0xffu & x);
    assert(expr.width() == 8);
    assert(expr.to_smt2(-1).find("bvmul") != std::string::npos);
    ctx.assert_(ctx.bv_eq(x, 1u));
    assert(ctx.to_smt2().find("(check-sat)") != std::string::npos);

    smt_wire::Context bools;
    auto p = bools.bool_var("p");
    assert(bools.bool_var("p") == p.as_term());
    auto rotated = ctx.bv_rotate_left(x, 3);
    assert(rotated.sort() == smt_wire::Sort::BV);

    std::vector<uint8_t> raw_wide(9, 0xff);
    smt_wire::Context masked;
    auto wide = masked.bv_const_wide(raw_wide, 65);
    assert(wide.width() == 65);

    bool threw = false;
    try { (void)ctx.bv_add(x, ctx.bv_var("y", 16)); } catch (const std::invalid_argument&) { threw = true; }
    assert(threw);
    return 0;
}
