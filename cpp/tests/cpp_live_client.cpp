#include <smt_wire/smt_wire.hpp>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <string>

int main(int argc, char** argv) {
    assert(argc == 3);
    const std::string host = argv[1];
    const auto port = static_cast<uint16_t>(std::stoul(argv[2]));

    smt_wire::Context ctx;
    auto x = ctx.bv_var("cpp_x", 4);
    ctx.assert_(ctx.bv_eq(x, 2u));

    smt_wire::Client client(host, port);
    auto response = client.solve(ctx, 0, true, false, 0x4001u);
    assert(response.request_id == 0x4001u);
    assert(response.status == smt_wire::Status::Sat);
    assert(response.has_model);
    auto value = response.model.get(x.as_term());
    assert(value != nullptr);
    assert(value->width == 4 && !value->bytes.empty() && value->bytes[0] == 2);

    auto text = client.smt2(
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
