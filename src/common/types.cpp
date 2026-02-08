#include "common/types.h"
#include "common/arena.h"

#include <sstream>

namespace delta {

// --- Logic4Word operations ---

Logic4Word logic4_and(Logic4Word a, Logic4Word b) {
    // Truth table: 0&x=0, 1&x=x, x&x=x
    uint64_t a_known_0 = ~a.aval & ~a.bval;
    uint64_t b_known_0 = ~b.aval & ~b.bval;
    uint64_t result_aval = a.aval & b.aval;
    uint64_t any_known_0 = a_known_0 | b_known_0;
    uint64_t result_bval = (a.bval | b.bval) & ~any_known_0;
    return {result_aval & ~result_bval, result_bval};
}

Logic4Word logic4_or(Logic4Word a, Logic4Word b) {
    // Truth table: 1|x=1, 0|x=x, x|x=x
    uint64_t a_known_1 = a.aval & ~a.bval;
    uint64_t b_known_1 = b.aval & ~b.bval;
    uint64_t result_aval = a.aval | b.aval;
    uint64_t any_known_1 = a_known_1 | b_known_1;
    uint64_t result_bval = (a.bval | b.bval) & ~any_known_1;
    return {result_aval | result_bval, result_bval};
}

Logic4Word logic4_xor(Logic4Word a, Logic4Word b) {
    uint64_t unknown = a.bval | b.bval;
    uint64_t result_aval = a.aval ^ b.aval;
    return {result_aval & ~unknown, unknown};
}

Logic4Word logic4_not(Logic4Word a) {
    return {~a.aval & ~a.bval, a.bval};
}

// --- Logic4Vec operations ---

bool Logic4Vec::is_known() const {
    for (uint32_t i = 0; i < nwords; ++i) {
        if (words[i].bval != 0) {
            return false;
        }
    }
    return true;
}

uint64_t Logic4Vec::to_uint64() const {
    if (nwords == 0) {
        return 0;
    }
    return words[0].aval;
}

std::string Logic4Vec::to_string() const {
    std::string result;
    result.reserve(width);
    for (int32_t i = static_cast<int32_t>(width) - 1; i >= 0; --i) {
        uint32_t word_idx = static_cast<uint32_t>(i) / 64;
        uint32_t bit_idx = static_cast<uint32_t>(i) % 64;
        uint64_t mask = uint64_t(1) << bit_idx;
        bool a = (words[word_idx].aval & mask) != 0;
        bool b = (words[word_idx].bval & mask) != 0;
        if (!b && !a) {
            result += '0';
        } else if (!b && a) {
            result += '1';
        } else if (b && !a) {
            result += 'x';
        } else {
            result += 'z';
        }
    }
    return result;
}

Logic4Vec make_logic4_vec(Arena& arena, uint32_t width) {
    uint32_t nwords = (width + 63) / 64;
    auto* words = arena.alloc_array<Logic4Word>(nwords);
    return {width, nwords, words};
}

Logic4Vec make_logic4_vec_val(Arena& arena, uint32_t width, uint64_t val) {
    auto vec = make_logic4_vec(arena, width);
    if (vec.nwords > 0) {
        vec.words[0].aval = val;
    }
    return vec;
}

// --- Logic2Vec ---

uint64_t Logic2Vec::to_uint64() const {
    if (nwords == 0) {
        return 0;
    }
    return words[0];
}

} // namespace delta
