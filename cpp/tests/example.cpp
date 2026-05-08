#include <smt_wire/smt_wire.hpp>

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

std::string status_name(smt_wire::Status status) {
    switch (status) {
        case smt_wire::Status::Simplified: return "Status::Simplified";
        case smt_wire::Status::Sat: return "Status::Sat";
        case smt_wire::Status::Unsat: return "Status::Unsat";
        case smt_wire::Status::Unknown: return "Status::Unknown";
        case smt_wire::Status::Error: return "Status::Error";
    }
    return "Status::<invalid>";
}

uint64_t scalar_u64(const smt_wire::ScalarValue& value) {
    uint64_t out = 0;
    const auto limit = value.bytes.size() < 8 ? value.bytes.size() : 8;
    for (size_t i = 0; i < limit; ++i) {
        out |= uint64_t(value.bytes[i]) << (8 * i);
    }
    return out;
}

std::string to_rpn(const smt_wire::Term& term) {
    switch (term.op()) {
        case smt_wire::Op::BV_VAR:
            return term.name();
        case smt_wire::Op::BV_CONST:
            return std::to_string(term.value()) + ":" + std::to_string(term.width());
        default:
            break;
    }

    std::vector<std::string> parts;
    for (const auto& child : term.children()) {
        parts.push_back(to_rpn(child));
    }
    parts.push_back(smt_wire::op_symbol(static_cast<uint8_t>(term.op())));

    std::ostringstream out;
    for (size_t i = 0; i < parts.size(); ++i) {
        if (i != 0) out << ' ';
        out << parts[i];
    }
    return out.str();
}

int main() {
    smt_wire::Context ctx;
    std::cout << "Context#" << ctx.id() << "\n";

    auto x = ctx.bv_var("x", 32);
    auto y = ctx.bv_var("y", 32);

    // Terms are thin handles. C++ operators forward to Context methods, and
    // integers are coerced to BV constants using the left term's width.
    auto x_plus_y = x + y;
    auto mba = (x ^ y) + ((x & y) * 2u);
    auto masked = 0xffu & (x + 3u);

    // Named operations live on Context: comparisons, structural operations, and Bool ops.
    auto identity_holds = ctx.bv_eq(mba, x_plus_y);
    auto low_x_is_42 = ctx.bv_eq(ctx.bv_extract(x, 7, 0), 42u);
    ctx.assert_(ctx.bool_and(identity_holds, low_x_is_42));

    std::cout << "MBA: " << mba.to_smt2(0) << "\n";
    std::cout << "MBA full: " << mba.to_smt2() << "\n";
    std::cout << "masked: " << masked.to_smt2() << "\n";
    std::cout << "RPN: " << to_rpn(mba.as_term()) << "\n";

    // Start the server first:
    //   cargo run -p smt-server -- 127.0.0.1:9123
    smt_wire::Client client("127.0.0.1", 9123);
    auto resp = client.solve(ctx);
    std::cout << status_name(resp.status) << "\n";
    if (resp.status == smt_wire::Status::Sat && resp.has_model) {
        auto items = resp.model.items();
        std::sort(items.begin(), items.end(), [](const auto& a, const auto& b) {
            return a.first.name() < b.first.name();
        });
        for (const auto& item : items) {
            std::cout << item.first.name() << " = 0x" << std::hex << scalar_u64(item.second) << std::dec << "\n";
        }
    }

    auto simplified = client.simplify(mba.as_term());
    if (simplified.has_term) {
        std::cout << "simplified MBA: " << simplified.term.to_smt2() << "\n";
    }

    std::cout << "\nSMT-LIB:\n";
    auto ctx_smt2 = ctx.to_smt2();
    std::cout << ctx_smt2 << "\n";

    auto smt_resp = client.smt2(ctx_smt2);
    std::cout << smt_resp << "\n";

    return 0;
}
