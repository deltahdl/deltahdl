#pragma once

#include <cstdint>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace delta {

// --- And-Inverter Graph (AIG) ---
//
// Core data structure for logic synthesis. Each node represents a two-input
// AND gate. Edges carry an optional complement (inversion) flag stored in
// the LSB of the literal encoding:
//   literal = (node_id << 1) | complement_bit
//
// Constant-false is represented by literal 0, constant-true by literal 1.

struct AigNode {
    uint32_t id = 0;
    uint32_t fanin0 = 0; // literal: LSB is complement flag
    uint32_t fanin1 = 0; // literal: LSB is complement flag
};

// --- Literal helpers ---

/// Construct a literal from a node id and complement flag.
inline uint32_t aig_lit(uint32_t id, bool compl_flag) {
    return (id << 1) | static_cast<uint32_t>(compl_flag);
}

/// Extract the node id from a literal.
inline uint32_t aig_var(uint32_t lit) {
    return lit >> 1;
}

/// Return true if the literal carries a complement.
inline bool aig_is_compl(uint32_t lit) {
    return (lit & 1u) != 0;
}

// --- AIG graph container ---

class AigGraph {
  public:
    static constexpr uint32_t kConstFalse = 0;
    static constexpr uint32_t kConstTrue = 1;

    AigGraph();

    /// Create a new primary input. Returns its literal.
    uint32_t add_input();

    /// Create a structurally-hashed AND node. Returns its literal.
    uint32_t add_and(uint32_t lit0, uint32_t lit1);

    /// Negate a literal (flip complement bit).
    uint32_t add_not(uint32_t lit) const;

    /// OR via De Morgan: a | b = ~(~a & ~b).
    uint32_t add_or(uint32_t a, uint32_t b);

    /// XOR: a ^ b = (a & ~b) | (~a & b).
    uint32_t add_xor(uint32_t a, uint32_t b);

    /// MUX: sel ? a : b = (sel & a) | (~sel & b).
    uint32_t add_mux(uint32_t sel, uint32_t a, uint32_t b);

    /// Register a primary output literal.
    void add_output(uint32_t lit);

    /// Register a latch: (current_state_lit, next_state_lit, init_value).
    void add_latch(uint32_t current, uint32_t next, uint32_t init);

    /// Total number of AIG nodes (including constant node).
    size_t node_count() const;

    // Public data — kept accessible for pass algorithms.
    std::vector<AigNode> nodes;
    std::vector<uint32_t> inputs;
    std::vector<uint32_t> outputs;
    std::vector<std::tuple<uint32_t, uint32_t, uint32_t>> latches;

  private:
    /// Pack two literals into a single 64-bit key for structural hashing.
    static uint64_t hash_key(uint32_t lit0, uint32_t lit1);

    /// Allocate a fresh node and return its id.
    uint32_t alloc_node();

    // Structural hash: maps (fanin0, fanin1) -> node id for dedup.
    std::unordered_map<uint64_t, uint32_t> strash_;
};

} // namespace delta
