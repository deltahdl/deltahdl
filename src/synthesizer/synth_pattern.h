#pragma once

#include <cstdint>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"

namespace delta {

class SynthLower;

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
