#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"

namespace delta {

class SynthLower;

// The bits an integer literal's digits write: the value of each bit position in
// `aval`, and the positions the literal wrote a don't-care digit at in
// `dc_mask`. Both are indexed by bit position and hold no entry above the
// highest position the digits reached, which §5.7.1 pads to the left with
// zeros. A position is addressed rather than a 64-bit word shifted, because
// §5.7.1 sizes a literal by its size constant and admits one wider than any
// integer C++ has: `128'h1_0000_0000_0000_0000` writes bit 64.
struct PatternBits {
  std::vector<bool> aval;
  std::vector<bool> dc_mask;

  // True where the literal was written with a base that gives each digit its
  // own bits, which is what makes `aval` the value. A decimal literal writes
  // no per-digit bits, so its value is the one the parser folded into
  // Expr::int_val rather than anything here.
  bool has_digits = false;

  // A decimal literal carrying a don't-care digit is don't-care throughout,
  // since no digit of it stands for a bit position.
  bool all_dont_care = false;
};

// §5.7.1: the bits `text` writes, over the digits that follow its base. Under
// `case_kind` the digits §12.5.1 makes don't-care are recorded in `dc_mask`
// rather than in `aval`; pass TokenKind::kKwCase to read every digit as a
// value.
PatternBits ParsePatternLiteral(std::string_view text, TokenKind case_kind);

// The value `bits` carries at bit position `b`, and false above every position
// its digits reached.
bool PatternBitValue(const PatternBits& bits, uint32_t b);

// The lowering engine objects threaded through the pattern-match family: the
// AIG being built and the SynthLower bit lowerer.
struct LowerCtx {
  AigGraph& aig;
  SynthLower& synth;
};

// The literal answering whether `sel_expr` matches `pat` over `sel_width` bits,
// with the bit positions `pat` wrote a don't-care digit at left out of the
// comparison. A pattern that is not an integer literal, and every pattern at
// all when `case_kind` is TokenKind::kKwCase, is compared bit for bit with no
// position left out.
//
// §12.5.1 gives the two case kinds that read don't-care digits: casez takes z
// and ? as don't-care, casex takes x as well. §11.4.6 makes `a ==? b` and
// `a !=? b` the same comparison with both x and z acting as wildcards, so a
// wildcard equality is built by calling this with TokenKind::kKwCasex.
uint32_t BuildPatternMatch(const Expr* sel_expr, const Expr* pat,
                           const LowerCtx& ctx, uint32_t sel_width,
                           TokenKind case_kind);

}  // namespace delta
