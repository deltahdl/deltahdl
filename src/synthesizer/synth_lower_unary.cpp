#include <cstdint>
#include <optional>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

struct ReductionRule {
  TokenKind folded = TokenKind::kEof;
  bool invert = false;
};

static ReductionRule ReductionRuleFor(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
      return {TokenKind::kAmp, false};
    case TokenKind::kTildeAmp:
      return {TokenKind::kAmp, true};
    case TokenKind::kPipe:
      return {TokenKind::kPipe, false};
    case TokenKind::kTildePipe:
      return {TokenKind::kPipe, true};
    case TokenKind::kCaret:
      return {TokenKind::kCaret, false};
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return {TokenKind::kCaret, true};
    default:
      return {};
  }
}

static uint32_t ReductionStep(AigGraph& aig, TokenKind folded, uint32_t left,
                              uint32_t right) {
  if (folded == TokenKind::kAmp) return aig.AddAnd(left, right);
  if (folded == TokenKind::kPipe) return aig.AddOr(left, right);
  return aig.AddXor(left, right);
}

uint32_t SynthLower::LowerReductionBit(const Expr* expr, AigGraph& aig,
                                       uint32_t bit) {
  if (bit > 0) return AigGraph::kConstFalse;

  std::optional<uint32_t> width = ExprWidth(expr->lhs);
  if (!width) {
    ReportExprUnlowered(expr,
                        "reduction operand has no width in the synthesizer, "
                        "so the reduction has no lowering",
                        Subclause("11.4.9"));
    return AigGraph::kConstFalse;
  }

  ReductionRule rule = ReductionRuleFor(expr->op);
  uint32_t result = LowerExprBit(expr->lhs, aig, 0);
  for (uint32_t b = 1; b < *width; ++b) {
    result = ReductionStep(aig, rule.folded, result,
                           LowerExprBit(expr->lhs, aig, b));
  }
  return rule.invert ? aig.AddNot(result) : result;
}

uint32_t SynthLower::LowerTruthValue(const Expr* expr, AigGraph& aig,
                                     Subclause subclause) {
  std::optional<uint32_t> width = ExprWidth(expr);
  if (!width) {
    ReportExprUnlowered(expr,
                        "operand has no width in the synthesizer, so whether "
                        "it is true has no lowering",
                        subclause);
    return AigGraph::kConstFalse;
  }
  uint32_t saved_width = propagated_width_;
  bool saved_signed = propagated_signed_;
  propagated_width_ = *width;
  propagated_signed_ = IsSignedExpr(expr);
  uint32_t any = AigGraph::kConstFalse;
  for (uint32_t b = 0; b < *width; ++b) {
    any = aig.AddOr(any, LowerExprBit(expr, aig, b));
  }
  propagated_width_ = saved_width;
  propagated_signed_ = saved_signed;
  return any;
}

uint32_t SynthLower::LowerNegateBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  uint32_t carry = AigGraph::kConstTrue;
  uint32_t sum = AigGraph::kConstFalse;
  for (uint32_t b = 0; b <= bit; ++b) {
    uint32_t complemented =
        aig.AddNot(LowerContextOperandBit(expr->lhs, aig, b));
    sum = FullAdderBit(aig, AigGraph::kConstFalse, complemented, carry);
  }
  return sum;
}

uint32_t SynthLower::LowerUnaryBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit) {
  if (expr->op == TokenKind::kTilde) {
    return aig.AddNot(LowerContextOperandBit(expr->lhs, aig, bit));
  }
  if (expr->op == TokenKind::kBang) {
    if (bit > 0) return AigGraph::kConstFalse;
    return aig.AddNot(LowerTruthValue(expr->lhs, aig, Subclause("11.4.7")));
  }
  if (expr->op == TokenKind::kPlus) {
    return LowerContextOperandBit(expr->lhs, aig, bit);
  }
  if (expr->op == TokenKind::kMinus) return LowerNegateBit(expr, aig, bit);
  if (ReductionRuleFor(expr->op).folded != TokenKind::kEof) {
    return LowerReductionBit(expr, aig, bit);
  }

  ReportExprUnlowered(
      expr,
      "unary operator has no lowering in the synthesizer and would be "
      "dropped from the netlist",
      Subclause::None());
  return AigGraph::kConstFalse;
}

}  // namespace delta
