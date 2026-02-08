#include "sim/net.h"

#include <cassert>

namespace delta {

// --- Wire/tri resolution ---
// Multiple drivers: if all agree, that value wins.
// Conflicting known bits produce X. Z is overridden by any driven value.

static Logic4Word resolve_wire_word(Logic4Word a, Logic4Word b) {
    // Identify Z bits in each operand (aval=1, bval=1)
    uint64_t a_z = a.aval & a.bval;
    uint64_t b_z = b.aval & b.bval;

    // Where one side is Z, take the other side
    uint64_t use_b = a_z & ~b_z;
    uint64_t use_a = b_z & ~a_z;
    uint64_t both_driven = ~a_z & ~b_z;

    // Where both are driven, check for conflict
    uint64_t aval_agree = ~(a.aval ^ b.aval) & both_driven;
    uint64_t bval_agree = ~(a.bval ^ b.bval) & both_driven;
    uint64_t agree = aval_agree & bval_agree;
    uint64_t conflict = both_driven & ~agree;

    Logic4Word result;
    // For agreed bits, use either side. For conflict, produce X (aval=0, bval=1).
    result.aval = (a.aval & use_a) | (b.aval & use_b) | (a.aval & agree);
    result.bval = (a.bval & use_a) | (b.bval & use_b) | (a.bval & agree) | conflict;
    result.aval &= ~conflict;

    // Where both are Z, result is Z
    uint64_t both_z = a_z & b_z;
    result.aval |= both_z;
    result.bval |= both_z;

    return result;
}

Logic4Vec resolve_wire(const SmallVec<Driver*>& drivers) {
    if (drivers.empty()) {
        return {};
    }
    if (drivers.size() == 1) {
        return drivers[0]->driven_value;
    }

    Logic4Vec result = drivers[0]->driven_value;
    for (size_t i = 1; i < drivers.size(); ++i) {
        const auto& other = drivers[i]->driven_value;
        uint32_t nwords = result.nwords;
        for (uint32_t w = 0; w < nwords; ++w) {
            result.words[w] = resolve_wire_word(result.words[w], other.words[w]);
        }
    }
    return result;
}

// --- Wired-AND resolution ---
// All driven (non-Z) values are ANDed together. Z bits are ignored.

static Logic4Word resolve_wand_word(Logic4Word a, Logic4Word b) {
    uint64_t a_z = a.aval & a.bval;
    uint64_t b_z = b.aval & b.bval;

    // If one side is Z, take the other
    if (a_z == ~uint64_t(0)) return b;
    if (b_z == ~uint64_t(0)) return a;

    return logic4_and(a, b);
}

Logic4Vec resolve_wand(const SmallVec<Driver*>& drivers) {
    if (drivers.empty()) {
        return {};
    }
    if (drivers.size() == 1) {
        return drivers[0]->driven_value;
    }

    Logic4Vec result = drivers[0]->driven_value;
    for (size_t i = 1; i < drivers.size(); ++i) {
        const auto& other = drivers[i]->driven_value;
        uint32_t nwords = result.nwords;
        for (uint32_t w = 0; w < nwords; ++w) {
            result.words[w] = resolve_wand_word(result.words[w], other.words[w]);
        }
    }
    return result;
}

// --- Wired-OR resolution ---
// All driven (non-Z) values are ORed together. Z bits are ignored.

static Logic4Word resolve_wor_word(Logic4Word a, Logic4Word b) {
    uint64_t a_z = a.aval & a.bval;
    uint64_t b_z = b.aval & b.bval;

    if (a_z == ~uint64_t(0)) return b;
    if (b_z == ~uint64_t(0)) return a;

    return logic4_or(a, b);
}

Logic4Vec resolve_wor(const SmallVec<Driver*>& drivers) {
    if (drivers.empty()) {
        return {};
    }
    if (drivers.size() == 1) {
        return drivers[0]->driven_value;
    }

    Logic4Vec result = drivers[0]->driven_value;
    for (size_t i = 1; i < drivers.size(); ++i) {
        const auto& other = drivers[i]->driven_value;
        uint32_t nwords = result.nwords;
        for (uint32_t w = 0; w < nwords; ++w) {
            result.words[w] = resolve_wor_word(result.words[w], other.words[w]);
        }
    }
    return result;
}

} // namespace delta
