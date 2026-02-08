#include "synth/aig.h"

#include <algorithm>

namespace delta {

// ---------------------------------------------------------------------------
// AigGraph
// ---------------------------------------------------------------------------

AigGraph::AigGraph() {
    // Node 0 is the constant-false node.
    AigNode constant{};
    constant.id = 0;
    constant.fanin0 = 0;
    constant.fanin1 = 0;
    nodes.push_back(constant);
}

uint32_t AigGraph::add_input() {
    uint32_t id = alloc_node();
    inputs.push_back(id);
    return aig_lit(id, false);
}

uint32_t AigGraph::add_and(uint32_t lit0, uint32_t lit1) {
    // Trivial cases: AND with constant.
    if (lit0 == kConstFalse || lit1 == kConstFalse) {
        return kConstFalse;
    }
    if (lit0 == kConstTrue) {
        return lit1;
    }
    if (lit1 == kConstTrue) {
        return lit0;
    }

    // Idempotent / complementary.
    if (lit0 == lit1) {
        return lit0;
    }
    if (aig_var(lit0) == aig_var(lit1)) {
        return kConstFalse;  // a & ~a = 0
    }

    // Canonicalize: smaller literal first.
    if (lit0 > lit1) {
        std::swap(lit0, lit1);
    }

    // Structural hashing lookup.
    uint64_t key = hash_key(lit0, lit1);
    auto it = strash_.find(key);
    if (it != strash_.end()) {
        return aig_lit(it->second, false);
    }

    // Create new AND node.
    uint32_t id = alloc_node();
    nodes[id].fanin0 = lit0;
    nodes[id].fanin1 = lit1;
    strash_[key] = id;

    return aig_lit(id, false);
}

uint32_t AigGraph::add_not(uint32_t lit) const {
    return lit ^ 1u;
}

uint32_t AigGraph::add_or(uint32_t a, uint32_t b) {
    // De Morgan: a | b = ~(~a & ~b)
    return add_not(add_and(add_not(a), add_not(b)));
}

uint32_t AigGraph::add_xor(uint32_t a, uint32_t b) {
    // a ^ b = (a & ~b) | (~a & b)
    uint32_t left = add_and(a, add_not(b));
    uint32_t right = add_and(add_not(a), b);
    return add_or(left, right);
}

uint32_t AigGraph::add_mux(uint32_t sel, uint32_t a, uint32_t b) {
    // sel ? a : b = (sel & a) | (~sel & b)
    uint32_t when_true = add_and(sel, a);
    uint32_t when_false = add_and(add_not(sel), b);
    return add_or(when_true, when_false);
}

void AigGraph::add_output(uint32_t lit) {
    outputs.push_back(lit);
}

void AigGraph::add_latch(uint32_t current, uint32_t next, uint32_t init) {
    latches.emplace_back(current, next, init);
}

size_t AigGraph::node_count() const {
    return nodes.size();
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

uint64_t AigGraph::hash_key(uint32_t lit0, uint32_t lit1) {
    return (static_cast<uint64_t>(lit0) << 32) | static_cast<uint64_t>(lit1);
}

uint32_t AigGraph::alloc_node() {
    uint32_t id = static_cast<uint32_t>(nodes.size());
    AigNode node{};
    node.id = id;
    nodes.push_back(node);
    return id;
}

} // namespace delta
