#pragma once

#include <cstdint>

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

class Arena;

// §11.6.1 gives a binary arithmetic operator a result as wide as its widest
// operand, and §11.4.3 defines the operators on the whole of that width. What a
// value holds beyond bit 63 is therefore part of the answer, and the machine
// word the operators computed in is not: reading an operand through
// Logic4Vec::ToUint64 takes words[0] alone and writing the result through
// MakeLogic4VecVal fills words[0] alone, so on a `logic [127:0]` the sum
// 128'h1_0000_0000_0000_0000 + 128'h1 read 1.
//
// `width` is the result width §11.6.1 settled and `is_signed` says which of
// §11.6.1's two interpretations the operands carry, since the two disagree
// above the sign bit and for division's rounding.
struct WideArithSpec {
  uint32_t width = 0;
  bool is_signed = false;
};

// Computes `op` over every word of two known operands. The caller has already
// answered §11.8.4's unknown-operand question, so neither operand carries an x
// or a z here. Division and modulus by zero answer with all x, as §11.4.3's
// "the result shall be x" requires, and every other result is masked to
// `width` so nothing above the declared width reads as set.
Logic4Vec EvalWideArith(TokenKind op, const Logic4Vec& lhs,
                        const Logic4Vec& rhs, const WideArithSpec& spec,
                        Arena& arena);

}  // namespace delta
