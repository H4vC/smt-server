#include <smt_wire/smt_wire.hpp>
#include <cassert>
#include <cstdint>
#include <limits>
#include <stdexcept>
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

    assert((smt_wire::ScalarValue{0, {1}}).to_u64() == 1);
    assert((smt_wire::ScalarValue{0, {1}}).to_i64() == 1);
    assert((smt_wire::ScalarValue{8, {0xff}}).to_u64() == 255);
    assert((smt_wire::ScalarValue{8, {0xff}}).to_i64() == -1);
    assert((smt_wire::ScalarValue{8, {0x80}}).to_i64() == -128);
    assert((smt_wire::ScalarValue{12, {0xff, 0x0f}}).to_u64() == 4095);
    assert((smt_wire::ScalarValue{12, {0xff, 0x0f}}).to_i64() == -1);
    assert((smt_wire::ScalarValue{12, {0x00, 0x08}}).to_i64() == -2048);
    assert((smt_wire::ScalarValue{12, {0xff, 0x07}}).to_i64() == 2047);
    assert((smt_wire::ScalarValue{64, {0, 0, 0, 0, 0, 0, 0, 0x80}}).to_i64() == std::numeric_limits<int64_t>::min());

    assert((smt_wire::ScalarValue{65, std::vector<uint8_t>(9, 0)}).to_u64() == 0);
    assert((smt_wire::ScalarValue{65, std::vector<uint8_t>(9, 0)}).to_i64() == 0);
    assert((smt_wire::ScalarValue{65, {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01}}).to_i64() == -1);

    bool scalar_threw = false;
    try { (void)(smt_wire::ScalarValue{65, {0, 0, 0, 0, 0, 0, 0, 0, 1}}).to_u64(); } catch (const std::overflow_error&) { scalar_threw = true; }
    assert(scalar_threw);
    scalar_threw = false;
    try { (void)(smt_wire::ScalarValue{65, {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0}}).to_i64(); } catch (const std::overflow_error&) { scalar_threw = true; }
    assert(scalar_threw);
    scalar_threw = false;
    try { (void)(smt_wire::ScalarValue{9, {0, 2}}).to_u64(); } catch (const std::invalid_argument&) { scalar_threw = true; }
    assert(scalar_threw);

    bool threw = false;
    try { (void)ctx.bv_add(x, ctx.bv_var("y", 16)); } catch (const std::invalid_argument&) { threw = true; }
    assert(threw);
    return 0;
}
