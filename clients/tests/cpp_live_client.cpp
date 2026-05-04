#include "../cpp/smt_wire.hpp"
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <string>

int main(int argc, char** argv) {
    assert(argc == 3);
    const std::string host = argv[1];
    const auto port = static_cast<uint16_t>(std::stoul(argv[2]));

    smt_wire::Builder b;
    auto x = b.bv_var("cpp_x", 4);
    b.assert_(b.bv_eq(x, b.bv_const(2, 4)));

    smt_wire::TcpClient client(host, port);
    auto response = client.send_request(b.build_solve_request(0x4001u, 0, true, false));
    assert(response.request_id == 0x4001u);
    assert(response.status == smt_wire::status::SAT);
    assert(response.flags == smt_wire::response_flags::HAS_MODEL);
    auto model = smt_wire::parse_model_payload(response.payload);
    bool saw_value = false;
    for (const auto& entry : model) {
        if (entry.value.width == 4 && !entry.value.bytes.empty() && entry.value.bytes[0] == 2) {
            saw_value = true;
        }
    }
    assert(saw_value);

    auto text = client.send_text(
        "(set-logic QF_BV)"
        "(declare-const |cpp y| (_ BitVec 2))"
        "(assert (= |cpp y| #b10))"
        "(check-sat)"
        "(get-value (|cpp y|))"
    );
    assert(text.find("sat\n") == 0);
    assert(text.find("(|cpp y| #b10)") != std::string::npos);
    return 0;
}
