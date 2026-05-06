#include "../cpp/smt_wire.hpp"
#include <cassert>
#include <cstdint>
#include <vector>

int main() {
    smt_wire::Builder b;
    auto x = b.bv_var("x", 8);
    auto one = b.bv_const(1, 8);
    b.assert_(b.bv_eq(x, one));
    auto bytes = b.build_solve_request(0x01020304u, 500, true, false);
    const std::vector<uint8_t> expected = {
        0x53,0x4d,0x54,0x51,0x04,0x03,0x02,0x01,0x00,0x01,0xf4,0x01,0x00,0x00,0x71,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x53,0x4d,0x54,0x00,0x01,0x00,0x00,0x00,0x03,0x00,0x00,0x00,0x02,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x01,0x00,0x00,0x00,0x08,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x1f,0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x78,0x02,0x00,0x00,0x80
    };
    assert(bytes == expected);
    auto simplify = b.build_simplify_request(2);
    assert(simplify[8] == smt_wire::command::SIMPLIFY);
    auto minimize = b.build_minimize_request(3, x, true, 0, true);
    assert(minimize[8] == smt_wire::command::MINIMIZE);
    auto rotated = b.bv_rotate_left(x, 3);
    assert(!smt_wire::is_bool_ref(rotated));
    smt_wire::Builder wide;
    wide.bv_const((uint64_t(1) << 63) | 3u, 65);
    auto wide_expr = wide.to_bytes();
    assert(smt_wire::read_u32(wide_expr, 16) == 9); // blob_len
    assert(smt_wire::read_u32(wide_expr, 48) == 9); // payload = blob ref (offset 0, len 9)
    std::vector<uint8_t> raw_wide(9, 0xff);
    smt_wire::Builder masked;
    masked.bv_const_wide(raw_wide, 65);
    auto masked_expr = masked.to_bytes();
    assert(masked_expr.back() == 1);
    std::vector<uint8_t> response = {'S','M','T','R', 7,0,0,0, smt_wire::status::ERROR, smt_wire::response_flags::HAS_MESSAGE, 3,0,0,0, 0,0, 'b','a','d'};
    auto parsed = smt_wire::parse_response(response);
    assert(parsed.request_id == 7 && parsed.status == smt_wire::status::ERROR && parsed.payload.size() == 3);
    bool bad_response_threw = false;
    try {
        std::vector<uint8_t> bad_response = {'S','M','T','R', 7,0,0,0, smt_wire::status::SAT, smt_wire::response_flags::HAS_CORE, 0,0,0,0, 0,0};
        (void)smt_wire::parse_response(bad_response);
    } catch (const std::invalid_argument&) { bad_response_threw = true; }
    assert(bad_response_threw);
    smt_wire::TcpClient client;
    client.set_max_response_bytes(8);
    assert(client.max_response_bytes() == 8);
    std::vector<uint8_t> model_payload;
    smt_wire::u32(model_payload, 1);
    smt_wire::u32(model_payload, x);
    smt_wire::u32(model_payload, 8);
    smt_wire::u32(model_payload, 1);
    model_payload.push_back(42);
    auto model = smt_wire::parse_model_payload(model_payload);
    assert(model.size() == 1 && model[0].node_ref == x && model[0].value.bytes[0] == 42);
    std::vector<uint8_t> core_payload;
    smt_wire::u32(core_payload, 1);
    smt_wire::u32(core_payload, 2);
    core_payload.push_back('a');
    core_payload.push_back('0');
    auto core = smt_wire::parse_core_payload(core_payload);
    assert(core.size() == 1 && core[0] == "a0");
    bool threw = false;
    try { (void)b.bv_add(x, b.bv_var("y", 16)); } catch (const std::invalid_argument&) { threw = true; }
    assert(threw);
    return 0;
}
