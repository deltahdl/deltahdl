#pragma once

#include <cstdint>

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

class Arena;

struct WideArithSpec {
  uint32_t width = 0;
  bool is_signed = false;
  bool exponent_is_signed = false;
};

Logic4Vec EvalWideArith(TokenKind op, const Logic4Vec& lhs,
                        const Logic4Vec& rhs, const WideArithSpec& spec,
                        Arena& arena);

}  // namespace delta
