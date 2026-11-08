#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"

namespace delta {

class SynthLower;

struct PatternBits {
  std::vector<bool> aval;
  std::vector<bool> dc_mask;

  bool dont_care_above = false;

  bool has_digits = false;

  bool all_dont_care = false;
};

PatternBits ParsePatternLiteral(std::string_view text, TokenKind case_kind);

bool PatternBitValue(const PatternBits& bits, uint32_t b);

struct LowerCtx {
  AigGraph& aig;
  SynthLower& synth;
};

uint32_t BuildPatternMatch(const Expr* sel_expr, const Expr* pat,
                           const LowerCtx& ctx, uint32_t sel_width,
                           TokenKind case_kind);

}  // namespace delta
