#pragma once
// Single-file C++17 builder for the SMT v1 wire format.
// No networking and no dependencies beyond the C++ standard library.

#include <climits>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <winsock2.h>
#include <ws2tcpip.h>
#ifdef _MSC_VER
#pragma comment(lib, "Ws2_32.lib")
#endif
#else
#include <cerrno>
#include <cstring>
#include <netdb.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>
#endif

#ifdef ERROR
#undef ERROR
#endif

namespace smt_wire {

constexpr uint32_t BOOL_BIT = 0x80000000u;
constexpr uint32_t INDEX_MASK = 0x7fffffffu;
constexpr uint32_t MAX_WIDTH = 65536u;
constexpr size_t DEFAULT_MAX_RESPONSE_BYTES = 64u * 1024u * 1024u;

namespace tag {
constexpr uint8_t BV_VAR = 0, BV_CONST = 1, BV_NOT = 2, BV_NEG = 3, BV_AND = 4, BV_OR = 5;
constexpr uint8_t BV_XOR = 6, BV_ADD = 7, BV_SUB = 8, BV_MUL = 9, BV_UDIV = 10, BV_UREM = 11;
constexpr uint8_t BV_SDIV = 12, BV_SREM = 13, BV_SMOD = 14, BV_SHL = 15, BV_LSHR = 16, BV_ASHR = 17;
constexpr uint8_t BV_EXTRACT = 18, BV_CONCAT = 19, BV_ZEXT = 20, BV_SEXT = 21, BV_ITE = 22, BV_SELECT = 23;
constexpr uint8_t BOOL_TRUE = 24, BOOL_FALSE = 25, BOOL_VAR = 26, BOOL_NOT = 27, BOOL_AND = 28, BOOL_OR = 29, BOOL_IMPLIES = 30;
constexpr uint8_t BV_EQ = 31, BV_ULT = 32, BV_ULE = 33, BV_SLT = 34, BV_SLE = 35;
constexpr uint8_t UADD_OVF = 36, SADD_OVF = 37, USUB_OVF = 38, SSUB_OVF = 39, UMUL_OVF = 40, SMUL_OVF = 41, NEG_OVF = 42, SDIV_OVF = 43;
} // namespace tag

namespace command { constexpr uint8_t SOLVE = 0, SIMPLIFY = 1, MINIMIZE = 2, MAXIMIZE = 3; }
namespace request_flags { constexpr uint8_t WANT_MODEL = 1u << 0, WANT_CORE = 1u << 1, SIGNED = 1u << 2; }
namespace status { constexpr uint8_t OK = 0, SAT = 1, UNSAT = 2, UNKNOWN = 3, ERROR = 4; }
namespace response_flags { constexpr uint8_t HAS_MODEL = 1u << 0, HAS_CORE = 1u << 1, HAS_EXPR = 1u << 2, HAS_VALUE = 1u << 3, HAS_MESSAGE = 1u << 4, ALL = HAS_MODEL | HAS_CORE | HAS_EXPR | HAS_VALUE | HAS_MESSAGE; }

inline uint32_t bv_ref(uint32_t index) { if (index > INDEX_MASK) throw std::invalid_argument("node index out of range"); return index; }
inline uint32_t bool_ref(uint32_t index) { if (index > INDEX_MASK) throw std::invalid_argument("node index out of range"); return BOOL_BIT | index; }
inline uint32_t ref_index(uint32_t ref) { return ref & INDEX_MASK; }
inline bool is_bool_ref(uint32_t ref) { return (ref & BOOL_BIT) != 0; }
inline uint64_t blob_payload(uint32_t offset, uint32_t len) { return (static_cast<uint64_t>(offset) << 32) | len; }
inline uint32_t bytes_for_width(uint32_t width) { if (width == 0 || width > MAX_WIDTH) throw std::invalid_argument("invalid width"); return (width + 7) / 8; }

inline void u8(std::vector<uint8_t>& out, uint8_t v) { out.push_back(v); }
inline void u16(std::vector<uint8_t>& out, uint16_t v) { out.push_back(uint8_t(v)); out.push_back(uint8_t(v >> 8)); }
inline void u32(std::vector<uint8_t>& out, uint32_t v) { for (int i = 0; i < 4; ++i) out.push_back(uint8_t(v >> (8 * i))); }
inline void u64(std::vector<uint8_t>& out, uint64_t v) { for (int i = 0; i < 8; ++i) out.push_back(uint8_t(v >> (8 * i))); }

struct Node { uint8_t tag, arity; uint16_t aux_hi; uint32_t width, aux_lo, children; uint64_t payload; };
struct Assertion { uint32_t root; bool named; uint32_t name_offset, name_len; };
struct Meta { bool is_bool; uint32_t width; };
struct ScalarValue { uint32_t width; std::vector<uint8_t> bytes; };
struct ModelEntry { uint32_t node_ref; ScalarValue value; };
struct SimplifyResult { std::vector<uint8_t> expression; uint32_t target_node; };
struct OptimizationResult { ScalarValue optimum; bool has_model; std::vector<ModelEntry> model; };
struct Response { uint32_t request_id; uint8_t status, flags; std::vector<uint8_t> payload; };

class Builder {
public:
    std::vector<Node> nodes;
    std::vector<uint32_t> children;
    std::vector<uint8_t> blob;
    std::vector<Meta> meta;
    std::vector<Assertion> assertions;
    std::vector<uint32_t> assumptions;
    std::vector<size_t> scopes;

    void reset() { *this = Builder(); }
    void push() { scopes.push_back(assertions.size()); }
    void pop() { if (scopes.empty()) throw std::invalid_argument("pop without push"); assertions.resize(scopes.back()); scopes.pop_back(); }

    uint32_t bv_var(const std::string& name, uint32_t width) { check_width(width); auto b = add_blob(name); return add(tag::BV_VAR, width, {}, 0, 0, blob_payload(b.first, b.second)); }
    uint32_t bool_var(const std::string& name) { auto b = add_blob(name); return add(tag::BOOL_VAR, 0, {}, 0, 0, blob_payload(b.first, b.second)); }
    uint32_t bool_true() { return add(tag::BOOL_TRUE, 0); }
    uint32_t bool_false() { return add(tag::BOOL_FALSE, 0); }

    uint32_t bv_const(uint64_t value, uint32_t width) {
        check_width(width);
        if (width <= 64) {
            if (width < 64) value &= ((uint64_t(1) << width) - 1);
            return add(tag::BV_CONST, width, {}, 0, 0, value);
        }
        std::vector<uint8_t> bytes(bytes_for_width(width), 0);
        for (size_t i = 0; i < 8; ++i) bytes[i] = uint8_t(value >> (8 * i));
        return bv_const_wide(bytes, width);
    }
    uint32_t bv_const_wide(const std::vector<uint8_t>& bytes, uint32_t width) {
        if (bytes.size() != bytes_for_width(width)) throw std::invalid_argument("wide constant length mismatch");
        std::vector<uint8_t> normalized = bytes;
        if (width % 8 != 0 && !normalized.empty()) normalized.back() &= uint8_t((1u << (width % 8)) - 1u);
        if (width <= 64) { uint64_t v = 0; for (size_t i = 0; i < normalized.size(); ++i) v |= uint64_t(normalized[i]) << (8 * i); return bv_const(v, width); }
        auto b = add_blob(normalized); return add(tag::BV_CONST, width, {}, 0, 0, blob_payload(b.first, b.second));
    }

    uint32_t bv_not(uint32_t x) { return bv_unary(tag::BV_NOT, x); }
    uint32_t bv_neg(uint32_t x) { return bv_unary(tag::BV_NEG, x); }
    uint32_t bv_and(uint32_t a, uint32_t b) { return bv_binary(tag::BV_AND, a, b); }
    uint32_t bv_or(uint32_t a, uint32_t b) { return bv_binary(tag::BV_OR, a, b); }
    uint32_t bv_xor(uint32_t a, uint32_t b) { return bv_binary(tag::BV_XOR, a, b); }
    uint32_t bv_add(uint32_t a, uint32_t b) { return bv_binary(tag::BV_ADD, a, b); }
    uint32_t bv_sub(uint32_t a, uint32_t b) { return bv_binary(tag::BV_SUB, a, b); }
    uint32_t bv_mul(uint32_t a, uint32_t b) { return bv_binary(tag::BV_MUL, a, b); }
    uint32_t bv_udiv(uint32_t a, uint32_t b) { return bv_binary(tag::BV_UDIV, a, b); }
    uint32_t bv_urem(uint32_t a, uint32_t b) { return bv_binary(tag::BV_UREM, a, b); }
    uint32_t bv_sdiv(uint32_t a, uint32_t b) { return bv_binary(tag::BV_SDIV, a, b); }
    uint32_t bv_srem(uint32_t a, uint32_t b) { return bv_binary(tag::BV_SREM, a, b); }
    uint32_t bv_smod(uint32_t a, uint32_t b) { return bv_binary(tag::BV_SMOD, a, b); }
    uint32_t bv_shl(uint32_t a, uint32_t b) { return bv_binary(tag::BV_SHL, a, b); }
    uint32_t bv_lshr(uint32_t a, uint32_t b) { return bv_binary(tag::BV_LSHR, a, b); }
    uint32_t bv_ashr(uint32_t a, uint32_t b) { return bv_binary(tag::BV_ASHR, a, b); }

    uint32_t bv_extract(uint32_t x, uint32_t hi, uint32_t lo) { uint32_t w = expect_bv(x); if (lo > hi || hi >= w || hi > 0xffff) throw std::invalid_argument("bad extract"); return add(tag::BV_EXTRACT, hi - lo + 1, {x}, uint16_t(hi), lo); }
    uint32_t bv_concat(uint32_t a, uint32_t b) { uint32_t w = expect_bv(a) + expect_bv(b); check_width(w); return add(tag::BV_CONCAT, w, {a, b}); }
    uint32_t bv_zext(uint32_t x, uint16_t amount) { return bv_ext(tag::BV_ZEXT, x, amount); }
    uint32_t bv_sext(uint32_t x, uint16_t amount) { return bv_ext(tag::BV_SEXT, x, amount); }
    uint32_t bv_ite(uint32_t c, uint32_t t, uint32_t e) { expect_bool(c); return add(tag::BV_ITE, same_bv(t, e), {c, t, e}); }
    uint32_t bv_select(const std::vector<uint32_t>& selectors, const std::vector<uint32_t>& values, uint32_t def) { if (selectors.size() != values.size() || selectors.size() > 127) throw std::invalid_argument("bad BV_SELECT pair count"); uint32_t w = expect_bv(def); std::vector<uint32_t> ch; for (size_t i = 0; i < selectors.size(); ++i) { expect_bool(selectors[i]); if (expect_bv(values[i]) != w) throw std::invalid_argument("BV_SELECT width mismatch"); ch.push_back(selectors[i]); ch.push_back(values[i]); } ch.push_back(def); return add(tag::BV_SELECT, w, ch, uint16_t(selectors.size())); }

    uint32_t bool_not(uint32_t x) { expect_bool(x); return add(tag::BOOL_NOT, 0, {x}); }
    uint32_t bool_and(uint32_t a, uint32_t b) { return bool_binary(tag::BOOL_AND, a, b); }
    uint32_t bool_or(uint32_t a, uint32_t b) { return bool_binary(tag::BOOL_OR, a, b); }
    uint32_t bool_implies(uint32_t a, uint32_t b) { return bool_binary(tag::BOOL_IMPLIES, a, b); }

    uint32_t bv_eq(uint32_t a, uint32_t b) { return bv_cmp(tag::BV_EQ, a, b); }
    uint32_t bv_ult(uint32_t a, uint32_t b) { return bv_cmp(tag::BV_ULT, a, b); }
    uint32_t bv_ule(uint32_t a, uint32_t b) { return bv_cmp(tag::BV_ULE, a, b); }
    uint32_t bv_slt(uint32_t a, uint32_t b) { return bv_cmp(tag::BV_SLT, a, b); }
    uint32_t bv_sle(uint32_t a, uint32_t b) { return bv_cmp(tag::BV_SLE, a, b); }
    uint32_t bv_ne(uint32_t a, uint32_t b) { return bool_not(bv_eq(a, b)); }
    uint32_t bv_ugt(uint32_t a, uint32_t b) { return bv_ult(b, a); }
    uint32_t bv_uge(uint32_t a, uint32_t b) { return bv_ule(b, a); }
    uint32_t bv_sgt(uint32_t a, uint32_t b) { return bv_slt(b, a); }
    uint32_t bv_sge(uint32_t a, uint32_t b) { return bv_sle(b, a); }
    uint32_t uadd_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::UADD_OVF, a, b); }
    uint32_t sadd_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::SADD_OVF, a, b); }
    uint32_t usub_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::USUB_OVF, a, b); }
    uint32_t ssub_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::SSUB_OVF, a, b); }
    uint32_t umul_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::UMUL_OVF, a, b); }
    uint32_t smul_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::SMUL_OVF, a, b); }
    uint32_t neg_ovf(uint32_t x) { expect_bv(x); return add(tag::NEG_OVF, 0, {x}); }
    uint32_t sdiv_ovf(uint32_t a, uint32_t b) { return bv_cmp(tag::SDIV_OVF, a, b); }
    uint32_t bool_eq(uint32_t a, uint32_t b) { expect_bool(a); expect_bool(b); return bool_and(bool_or(a, bool_not(b)), bool_or(bool_not(a), b)); }
    uint32_t bool_xor(uint32_t a, uint32_t b) { return bool_not(bool_eq(a, b)); }
    uint32_t bool_ite(uint32_t c, uint32_t t, uint32_t e) { expect_bool(c); expect_bool(t); expect_bool(e); return bool_or(bool_and(c, t), bool_and(bool_not(c), e)); }
    uint32_t bv_rotate_left(uint32_t x, uint64_t amount) { uint32_t w = expect_bv(x); amount %= w; if (amount == 0) return x; return bv_or(bv_shl(x, bv_const(amount, w)), bv_lshr(x, bv_const(uint64_t(w) - amount, w))); }
    uint32_t bv_rotate_right(uint32_t x, uint64_t amount) { uint32_t w = expect_bv(x); amount %= w; if (amount == 0) return x; return bv_or(bv_lshr(x, bv_const(amount, w)), bv_shl(x, bv_const(uint64_t(w) - amount, w))); }

    void assert_(uint32_t root) { expect_bool(root); assertions.push_back({root, false, 0, 0}); }
    void assert_named(const std::string& name, uint32_t root) { expect_bool(root); auto b = add_blob(name); assertions.push_back({root, true, b.first, b.second}); }
    void assume(uint32_t root) { expect_bool(root); assumptions.push_back(root); }
    void clear_assumptions() { assumptions.clear(); }
    void assert_mutex(const std::vector<uint32_t>& sels) { for (auto s: sels) expect_bool(s); for (size_t i = 0; i < sels.size(); ++i) for (size_t j = i + 1; j < sels.size(); ++j) assert_(bool_not(bool_and(sels[i], sels[j]))); }

    std::vector<uint8_t> to_bytes() const { return expr_bytes(nodes, children, blob); }
    std::vector<uint8_t> build_solve_request(uint32_t request_id, uint32_t budget_ms = 0, bool want_model = false, bool want_core = false) const { return build_request(request_id, command::SOLVE, (want_model ? request_flags::WANT_MODEL : 0) | (want_core ? request_flags::WANT_CORE : 0), budget_ms, 0, false); }
    std::vector<uint8_t> build_simplify_request(uint32_t request_id, uint32_t target) const { meta_for(target); return build_request(request_id, command::SIMPLIFY, 0, 0, target, true); }
    std::vector<uint8_t> build_minimize_request(uint32_t request_id, uint32_t target, bool signed_order = false, uint32_t budget_ms = 0, bool want_model = false) const { expect_bv(target); return build_request(request_id, command::MINIMIZE, (signed_order ? request_flags::SIGNED : 0) | (want_model ? request_flags::WANT_MODEL : 0), budget_ms, target, true); }
    std::vector<uint8_t> build_maximize_request(uint32_t request_id, uint32_t target, bool signed_order = false, uint32_t budget_ms = 0, bool want_model = false) const { expect_bv(target); return build_request(request_id, command::MAXIMIZE, (signed_order ? request_flags::SIGNED : 0) | (want_model ? request_flags::WANT_MODEL : 0), budget_ms, target, true); }

private:
    static void check_width(uint32_t w) { if (w == 0 || w > MAX_WIDTH) throw std::invalid_argument("invalid BV width"); }
    bool tag_is_bool(uint8_t t) const { return t >= tag::BOOL_TRUE; }
    std::pair<uint32_t,uint32_t> add_blob(const std::string& s) { return add_blob(std::vector<uint8_t>(s.begin(), s.end())); }
    std::pair<uint32_t,uint32_t> add_blob(const std::vector<uint8_t>& data) { uint32_t off = uint32_t(blob.size()); blob.insert(blob.end(), data.begin(), data.end()); return {off, uint32_t(data.size())}; }
    uint32_t add(uint8_t t, uint32_t width, std::vector<uint32_t> child_refs = {}, uint16_t aux_hi = 0, uint32_t aux_lo = 0, uint64_t payload = 0) { for (auto c : child_refs) meta_for(c); uint32_t start = child_refs.empty() ? 0 : uint32_t(children.size()); children.insert(children.end(), child_refs.begin(), child_refs.end()); uint32_t idx = uint32_t(nodes.size()); nodes.push_back({t, uint8_t(child_refs.size()), aux_hi, width, aux_lo, start, payload}); bool ib = tag_is_bool(t); meta.push_back({ib, width}); return ib ? bool_ref(idx) : bv_ref(idx); }
    Meta meta_for(uint32_t ref) const { uint32_t idx = ref_index(ref); if (idx >= meta.size()) throw std::invalid_argument("bad node ref"); Meta m = meta[idx]; if (m.is_bool != is_bool_ref(ref)) throw std::invalid_argument("sort bit mismatch"); return m; }
    uint32_t expect_bv(uint32_t r) const { Meta m = meta_for(r); if (m.is_bool) throw std::invalid_argument("expected BV"); return m.width; }
    void expect_bool(uint32_t r) const { if (!meta_for(r).is_bool) throw std::invalid_argument("expected Bool"); }
    uint32_t same_bv(uint32_t a, uint32_t b) const { uint32_t aw = expect_bv(a), bw = expect_bv(b); if (aw != bw) throw std::invalid_argument("BV width mismatch"); return aw; }
    uint32_t bv_unary(uint8_t t, uint32_t x) { return add(t, expect_bv(x), {x}); }
    uint32_t bv_binary(uint8_t t, uint32_t a, uint32_t b) { return add(t, same_bv(a,b), {a,b}); }
    uint32_t bv_ext(uint8_t t, uint32_t x, uint16_t n) { uint32_t w = expect_bv(x) + n; check_width(w); return add(t, w, {x}, n); }
    uint32_t bool_binary(uint8_t t, uint32_t a, uint32_t b) { expect_bool(a); expect_bool(b); return add(t, 0, {a,b}); }
    uint32_t bv_cmp(uint8_t t, uint32_t a, uint32_t b) { same_bv(a,b); return add(t, 0, {a,b}); }

    static std::vector<uint8_t> expr_bytes(const std::vector<Node>& ns, const std::vector<uint32_t>& cs, const std::vector<uint8_t>& bl) { std::vector<uint8_t> out; out.insert(out.end(), {'S','M','T',0,1,0,0,0}); u32(out, uint32_t(ns.size())); u32(out, uint32_t(cs.size())); u32(out, uint32_t(bl.size())); for (int i=0;i<12;++i) u8(out,0); for (const auto& n: ns) { u8(out,n.tag); u8(out,n.arity); u16(out,n.aux_hi); u32(out,n.width); u32(out,n.aux_lo); u32(out,n.children); u64(out,n.payload); } for (auto c: cs) u32(out,c); out.insert(out.end(), bl.begin(), bl.end()); return out; }
    void mark(uint32_t ref, std::vector<uint8_t>& live) const { uint32_t idx = ref_index(ref); if (idx >= nodes.size()) throw std::invalid_argument("bad root ref"); if (live[idx]) return; live[idx] = 1; const Node& n = nodes[idx]; for (uint32_t i = 0; i < n.arity; ++i) mark(children[n.children + i], live); }
    std::vector<uint8_t> compact_expr(const std::vector<uint32_t>& roots, std::vector<uint32_t>& old_to_new) const { std::vector<uint8_t> live(nodes.size(), 0); for (auto r: roots) mark(r, live); old_to_new.assign(nodes.size(), UINT32_MAX); uint32_t next = 0; for (size_t old = 0; old < nodes.size(); ++old) if (live[old]) old_to_new[old] = meta[old].is_bool ? bool_ref(next++) : bv_ref(next++); std::vector<Node> ns; std::vector<uint32_t> cs; for (size_t old = 0; old < nodes.size(); ++old) if (live[old]) { Node n = nodes[old]; uint32_t start = n.arity ? uint32_t(cs.size()) : 0; for (uint32_t i = 0; i < n.arity; ++i) cs.push_back(old_to_new[ref_index(children[n.children + i])]); n.children = start; ns.push_back(n); } return expr_bytes(ns, cs, blob); }
    uint32_t remap(uint32_t ref, const std::vector<uint32_t>& old_to_new) const { uint32_t idx = ref_index(ref); if (idx >= old_to_new.size() || old_to_new[idx] == UINT32_MAX) throw std::invalid_argument("dead node ref"); return old_to_new[idx]; }
    std::vector<uint8_t> build_request(uint32_t request_id, uint8_t cmd, uint8_t flags, uint32_t budget, uint32_t target, bool has_target) const { std::vector<Assertion> named, ordered; std::vector<uint32_t> request_assumptions; if (cmd != command::SIMPLIFY) { std::vector<Assertion> unnamed; for (auto a: assertions) (a.named ? named : unnamed).push_back(a); ordered = named; ordered.insert(ordered.end(), unnamed.begin(), unnamed.end()); request_assumptions = assumptions; } else if (!has_target) { throw std::invalid_argument("SIMPLIFY requires a target expression"); } std::vector<uint32_t> roots; for (auto a: ordered) roots.push_back(a.root); roots.insert(roots.end(), request_assumptions.begin(), request_assumptions.end()); if (has_target) roots.push_back(target); std::vector<uint32_t> old_to_new; auto expr = compact_expr(roots, old_to_new); std::vector<uint8_t> out; out.insert(out.end(), {'S','M','T','Q'}); u32(out, request_id); u8(out, cmd); u8(out, flags); u32(out, budget); u32(out, uint32_t(expr.size())); u16(out, uint16_t(ordered.size())); u16(out, uint16_t(named.size())); u16(out, uint16_t(request_assumptions.size())); u32(out, has_target ? remap(target, old_to_new) : 0); u32(out, 0); out.insert(out.end(), expr.begin(), expr.end()); for (auto a: ordered) u32(out, remap(a.root, old_to_new)); for (auto a: named) { u32(out, a.name_offset); u32(out, a.name_len); } for (auto a: request_assumptions) u32(out, remap(a, old_to_new)); return out; }
};

inline std::vector<uint8_t> frame(const std::vector<uint8_t>& payload) { if (payload.size() > UINT32_MAX) throw std::invalid_argument("frame payload too large"); std::vector<uint8_t> out; u32(out, uint32_t(payload.size())); out.insert(out.end(), payload.begin(), payload.end()); return out; }
inline uint16_t read_u16(const std::vector<uint8_t>& data, size_t off) { if (off + 2 > data.size()) throw std::invalid_argument("short u16"); return uint16_t(data[off]) | (uint16_t(data[off+1]) << 8); }
inline uint32_t read_u32(const std::vector<uint8_t>& data, size_t off) { if (off + 4 > data.size()) throw std::invalid_argument("short u32"); return uint32_t(data[off]) | (uint32_t(data[off+1]) << 8) | (uint32_t(data[off+2]) << 16) | (uint32_t(data[off+3]) << 24); }
inline void require_bytes(const std::vector<uint8_t>& data, size_t off, size_t len, const char* what) { if (off > data.size() || len > data.size() - off) throw std::invalid_argument(what); }
inline ScalarValue parse_scalar_value(const std::vector<uint8_t>& data, size_t& off) { require_bytes(data, off, 8, "short scalar"); uint32_t width = read_u32(data, off); uint32_t len = read_u32(data, off + 4); off += 8; require_bytes(data, off, len, "short scalar value"); ScalarValue value{width, std::vector<uint8_t>(data.begin() + off, data.begin() + off + len)}; off += len; if (width == 0) { if (len != 1 || (value.bytes[0] != 0 && value.bytes[0] != 1)) throw std::invalid_argument("bad Bool scalar"); } else { uint32_t expected = bytes_for_width(width); if (len != expected) throw std::invalid_argument("bad BV scalar length"); uint32_t valid = width % 8; if (valid != 0 && !value.bytes.empty() && (value.bytes.back() & ~uint8_t((1u << valid) - 1u)) != 0) throw std::invalid_argument("bad BV scalar high bits"); } return value; }
inline std::vector<ModelEntry> parse_model_payload(const std::vector<uint8_t>& payload) { require_bytes(payload, 0, 4, "short model"); uint32_t count = read_u32(payload, 0); size_t off = 4; std::vector<ModelEntry> entries; entries.reserve(count); for (uint32_t i = 0; i < count; ++i) { require_bytes(payload, off, 4, "short model entry"); uint32_t ref = read_u32(payload, off); off += 4; entries.push_back({ref, parse_scalar_value(payload, off)}); } if (off != payload.size()) throw std::invalid_argument("trailing model bytes"); return entries; }
inline std::vector<std::string> parse_core_payload(const std::vector<uint8_t>& payload) { require_bytes(payload, 0, 4, "short core"); uint32_t count = read_u32(payload, 0); size_t off = 4; std::vector<std::string> names; names.reserve(count); for (uint32_t i = 0; i < count; ++i) { require_bytes(payload, off, 4, "short core name length"); uint32_t len = read_u32(payload, off); off += 4; require_bytes(payload, off, len, "short core name"); names.emplace_back(payload.begin() + off, payload.begin() + off + len); off += len; } if (off != payload.size()) throw std::invalid_argument("trailing core bytes"); return names; }
inline SimplifyResult parse_simplify_payload(const std::vector<uint8_t>& payload) { require_bytes(payload, 0, 8, "short simplify"); uint32_t expr_len = read_u32(payload, 0); uint32_t target_node = read_u32(payload, 4); size_t off = 8; require_bytes(payload, off, expr_len, "short simplify expression"); SimplifyResult result; result.target_node = target_node; result.expression.assign(payload.begin() + off, payload.begin() + off + expr_len); off += expr_len; if (off != payload.size()) throw std::invalid_argument("trailing simplify bytes"); return result; }
inline OptimizationResult parse_optimization_payload(const std::vector<uint8_t>& payload, bool has_model) { size_t off = 0; OptimizationResult result{parse_scalar_value(payload, off), has_model, {}}; if (has_model) { std::vector<uint8_t> rest(payload.begin() + off, payload.end()); result.model = parse_model_payload(rest); off = payload.size(); } if (off != payload.size()) throw std::invalid_argument("trailing optimization bytes"); return result; }
inline void validate_response_payload(uint8_t st, uint8_t flags, const std::vector<uint8_t>& payload) {
    if ((flags & ~response_flags::ALL) != 0) throw std::invalid_argument("unknown response flags");
    if (st == status::ERROR) {
        if (flags != response_flags::HAS_MESSAGE) throw std::invalid_argument("bad ERROR flags");
        (void)std::string(payload.begin(), payload.end());
    } else if (st == status::UNKNOWN) {
        if (flags == 0) { if (!payload.empty()) throw std::invalid_argument("UNKNOWN payload without HAS_MESSAGE"); }
        else if (flags == response_flags::HAS_MESSAGE) { (void)std::string(payload.begin(), payload.end()); }
        else throw std::invalid_argument("bad UNKNOWN flags");
    } else if (st == status::SAT) {
        uint8_t allowed = response_flags::HAS_MODEL | response_flags::HAS_VALUE;
        if ((flags & ~allowed) != 0) throw std::invalid_argument("bad SAT flags");
        bool has_value = (flags & response_flags::HAS_VALUE) != 0;
        bool has_model = (flags & response_flags::HAS_MODEL) != 0;
        if (!has_value && !has_model) { if (!payload.empty()) throw std::invalid_argument("SAT payload without flags"); }
        else if (has_value) { (void)parse_optimization_payload(payload, has_model); }
        else { (void)parse_model_payload(payload); }
    } else if (st == status::UNSAT) {
        if (flags == 0) { if (!payload.empty()) throw std::invalid_argument("UNSAT payload without HAS_CORE"); }
        else if (flags == response_flags::HAS_CORE) { (void)parse_core_payload(payload); }
        else throw std::invalid_argument("bad UNSAT flags");
    } else if (st == status::OK) {
        if (flags != response_flags::HAS_EXPR) throw std::invalid_argument("bad OK flags");
        (void)parse_simplify_payload(payload);
    } else {
        throw std::invalid_argument("unknown response status");
    }
}
inline Response parse_response(const std::vector<uint8_t>& data) {
    if (data.size() < 16 || data[0] != 'S' || data[1] != 'M' || data[2] != 'T' || data[3] != 'R') throw std::invalid_argument("bad response");
    uint32_t len = read_u32(data, 10);
    if (read_u16(data, 14) != 0) throw std::invalid_argument("response reserved field is not zero");
    if (data.size() != 16u + len) throw std::invalid_argument("response length mismatch");
    Response response{read_u32(data, 4), data[8], data[9], std::vector<uint8_t>(data.begin() + 16, data.end())};
    validate_response_payload(response.status, response.flags, response.payload);
    return response;
}

namespace detail {
#ifdef _WIN32
using socket_handle = SOCKET;
constexpr socket_handle invalid_socket = INVALID_SOCKET;
inline void ensure_socket_runtime() { struct Wsa { Wsa() { WSADATA data; if (WSAStartup(MAKEWORD(2, 2), &data) != 0) throw std::runtime_error("WSAStartup failed"); } ~Wsa() { WSACleanup(); } }; static Wsa wsa; (void)wsa; }
inline void close_socket(socket_handle s) { if (s != invalid_socket) closesocket(s); }
inline int last_socket_error() { return WSAGetLastError(); }
inline std::string socket_error_text(int code) { return "socket error " + std::to_string(code); }
inline std::string gai_error_text(int code) { return gai_strerrorA(code); }
#else
using socket_handle = int;
constexpr socket_handle invalid_socket = -1;
inline void ensure_socket_runtime() {}
inline void close_socket(socket_handle s) { if (s != invalid_socket) ::close(s); }
inline int last_socket_error() { return errno; }
inline std::string socket_error_text(int code) { return std::strerror(code); }
inline std::string gai_error_text(int code) { return gai_strerror(code); }
#endif
inline void throw_socket_error(const char* action) { throw std::runtime_error(std::string(action) + ": " + socket_error_text(last_socket_error())); }
inline void set_socket_timeout_ms(socket_handle s, int opt, int milliseconds) {
#ifdef _WIN32
    DWORD timeout = milliseconds < 0 ? 0u : static_cast<DWORD>(milliseconds);
    if (::setsockopt(s, SOL_SOCKET, opt, reinterpret_cast<const char*>(&timeout), sizeof(timeout)) != 0) throw_socket_error("setsockopt");
#else
    timeval tv{};
    if (milliseconds >= 0) { tv.tv_sec = milliseconds / 1000; tv.tv_usec = (milliseconds % 1000) * 1000; }
    if (::setsockopt(s, SOL_SOCKET, opt, &tv, sizeof(tv)) != 0) throw_socket_error("setsockopt");
#endif
}
} // namespace detail

class TcpClient {
public:
    TcpClient() = default;
    TcpClient(const std::string& host, uint16_t port) { open(host, port); }
    ~TcpClient() { close(); }
    TcpClient(const TcpClient&) = delete;
    TcpClient& operator=(const TcpClient&) = delete;
    TcpClient(TcpClient&& other) noexcept : sock_(other.sock_) { other.sock_ = detail::invalid_socket; }
    TcpClient& operator=(TcpClient&& other) noexcept { if (this != &other) { close(); sock_ = other.sock_; other.sock_ = detail::invalid_socket; } return *this; }

    static TcpClient connect(const std::string& host, uint16_t port) { return TcpClient(host, port); }
    bool connected() const { return sock_ != detail::invalid_socket; }
    void set_max_response_bytes(size_t max_response_bytes) { max_response_bytes_ = max_response_bytes; }
    size_t max_response_bytes() const { return max_response_bytes_; }
    void set_read_timeout_ms(int milliseconds) { require_connected(); detail::set_socket_timeout_ms(sock_, SO_RCVTIMEO, milliseconds); }
    void set_write_timeout_ms(int milliseconds) { require_connected(); detail::set_socket_timeout_ms(sock_, SO_SNDTIMEO, milliseconds); }

    void open(const std::string& host, uint16_t port) {
        close();
        detail::ensure_socket_runtime();
        addrinfo hints{};
        hints.ai_family = AF_UNSPEC;
        hints.ai_socktype = SOCK_STREAM;
        hints.ai_protocol = IPPROTO_TCP;
        addrinfo* result = nullptr;
        const std::string service = std::to_string(port);
        int rc = getaddrinfo(host.c_str(), service.c_str(), &hints, &result);
        if (rc != 0) throw std::runtime_error("getaddrinfo failed: " + detail::gai_error_text(rc));
        for (addrinfo* ai = result; ai != nullptr; ai = ai->ai_next) {
            detail::socket_handle s = ::socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
            if (s == detail::invalid_socket) continue;
#ifndef _WIN32
#ifdef SO_NOSIGPIPE
            int no_sigpipe = 1;
            (void)setsockopt(s, SOL_SOCKET, SO_NOSIGPIPE, &no_sigpipe, sizeof(no_sigpipe));
#endif
#endif
#ifdef _WIN32
            const int addr_len = static_cast<int>(ai->ai_addrlen);
#else
            const socklen_t addr_len = static_cast<socklen_t>(ai->ai_addrlen);
#endif
            if (::connect(s, ai->ai_addr, addr_len) == 0) { sock_ = s; break; }
            detail::close_socket(s);
        }
        freeaddrinfo(result);
        if (!connected()) throw std::runtime_error("connect failed");
    }

    void close() { detail::close_socket(sock_); sock_ = detail::invalid_socket; }

    void send_all(const uint8_t* data, size_t len) {
        require_connected();
        while (len > 0) {
#ifdef _WIN32
            int chunk = len > static_cast<size_t>(INT_MAX) ? INT_MAX : static_cast<int>(len);
            int sent = ::send(sock_, reinterpret_cast<const char*>(data), chunk, 0);
#else
            int flags = 0;
#ifdef MSG_NOSIGNAL
            flags = MSG_NOSIGNAL;
#endif
            ssize_t sent = ::send(sock_, data, len, flags);
#endif
            if (sent <= 0) detail::throw_socket_error("send");
            data += static_cast<size_t>(sent);
            len -= static_cast<size_t>(sent);
        }
    }

    std::vector<uint8_t> recv_exact(size_t len) {
        require_connected();
        std::vector<uint8_t> out(len);
        size_t off = 0;
        while (off < len) {
#ifdef _WIN32
            int chunk = (len - off) > static_cast<size_t>(INT_MAX) ? INT_MAX : static_cast<int>(len - off);
            int got = ::recv(sock_, reinterpret_cast<char*>(out.data() + off), chunk, 0);
#else
            ssize_t got = ::recv(sock_, out.data() + off, len - off, 0);
#endif
            if (got == 0) throw std::runtime_error("connection closed while reading frame");
            if (got < 0) detail::throw_socket_error("recv");
            off += static_cast<size_t>(got);
        }
        return out;
    }

    std::vector<uint8_t> send_payload(const std::vector<uint8_t>& payload) {
        auto framed = frame(payload);
        send_all(framed.data(), framed.size());
        auto header = recv_exact(4);
        uint32_t len = read_u32(header, 0);
        if (len > max_response_bytes_) throw std::runtime_error("response frame exceeds configured maximum");
        return recv_exact(len);
    }

    Response send_request(const std::vector<uint8_t>& request) { return parse_response(send_payload(request)); }

    std::string send_text(const std::string& script) {
        std::vector<uint8_t> payload(script.begin(), script.end());
        auto response = send_payload(payload);
        return std::string(response.begin(), response.end());
    }

private:
    detail::socket_handle sock_ = detail::invalid_socket;
    size_t max_response_bytes_ = DEFAULT_MAX_RESPONSE_BYTES;
    void require_connected() const { if (!connected()) throw std::runtime_error("TCP client is not connected"); }
};

} // namespace smt_wire
