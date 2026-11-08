#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"
#include "synthesizer/synth_pattern.h"

namespace delta {

bool IsCompareOp(TokenKind op) {
  switch (op) {
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
      return true;
    default:
      return false;
  }
}

static bool ComparesExchangedOperands(TokenKind op) {
  return op == TokenKind::kGt || op == TokenKind::kLtEq;
}

static bool ComparesNegated(TokenKind op) {
  switch (op) {
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kBangEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kBangEqQuestion:
      return true;
    default:
      return false;
  }
}

static bool ComparesForEquality(TokenKind op) {
  switch (op) {
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
      return true;
    default:
      return false;
  }
}

static bool ComparesWithWildcards(TokenKind op) {
  return op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static constexpr uint32_t kLiteralBits = 64;

uint32_t SynthLower::CompareWidth(const Expr* lhs, const Expr* rhs) {
  return std::max(kLiteralBits, std::max(ExprWidth(lhs).value_or(0),
                                         ExprWidth(rhs).value_or(0)));
}

uint32_t SynthLower::LowerExtendedOperandBit(const Expr* expr, AigGraph& aig,
                                             uint32_t bit, bool sign_extend) {
  uint32_t width = ExtendedOperandWidth(expr);
  if (width == 0 || bit < width) return LowerExprBit(expr, aig, bit);
  if (sign_extend) return LowerExprBit(expr, aig, width - 1);
  return AigGraph::kConstFalse;
}

uint32_t SynthLower::ExtendedOperandWidth(const Expr* expr) {
  if (expr->kind == ExprKind::kIdentifier) return SignalWidth(expr->text);
  if (expr->kind == ExprKind::kIntegerLiteral) {
    if (expr->text.find('\'') == std::string_view::npos) return 0;
    return ExprWidth(expr).value_or(0);
  }
  if (!ExprWidth(expr)) return 0;
  return propagated_width_;
}

uint32_t SynthLower::CompareEqual(const Expr* lhs, const Expr* rhs,
                                  AigGraph& aig, uint32_t width,
                                  bool is_signed) {
  uint32_t eq = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t l = LowerExtendedOperandBit(lhs, aig, b, is_signed);
    uint32_t r = LowerExtendedOperandBit(rhs, aig, b, is_signed);
    eq = aig.AddAnd(eq, aig.AddNot(aig.AddXor(l, r)));
  }
  return eq;
}

uint32_t SynthLower::CompareAtLeast(const Expr* lhs, const Expr* rhs,
                                    AigGraph& aig, uint32_t width,
                                    bool is_signed) {
  uint32_t carry = AigGraph::kConstTrue;
  for (uint32_t b = 0; b < width; ++b) {
    uint32_t l = LowerExtendedOperandBit(lhs, aig, b, is_signed);
    uint32_t r = aig.AddNot(LowerExtendedOperandBit(rhs, aig, b, is_signed));
    if (is_signed && b + 1 == width) {
      l = aig.AddNot(l);
      r = aig.AddNot(r);
    }
    FullAdderBit(aig, l, r, carry);
  }
  return carry;
}

static bool IsUnboundedRangeBound(const Expr* bound) {
  return bound == nullptr ||
         (bound->kind == ExprKind::kIdentifier && bound->text == "$");
}

uint32_t SynthLower::LowerInsideRangeMatch(const Expr* sel_expr,
                                           const Expr* range, AigGraph& aig,
                                           uint32_t width) {
  if (range->op != TokenKind::kEof) {
    ReportExprUnlowered(range,
                        "a value range written with a tolerance has no "
                        "lowering in the synthesizer",
                        Subclause("11.4.13"));
    return AigGraph::kConstFalse;
  }
  if (IsUnboundedRangeBound(range->index) ||
      IsUnboundedRangeBound(range->index_end)) {
    ReportExprUnlowered(range,
                        "a value range bounded by '$' has no lowering in the "
                        "synthesizer",
                        Subclause("11.4.13"));
    return AigGraph::kConstFalse;
  }
  bool is_signed = IsSignedExpr(sel_expr) && IsSignedExpr(range->index) &&
                   IsSignedExpr(range->index_end);
  bool saved_signed = propagated_signed_;
  propagated_signed_ = is_signed;
  uint32_t at_least =
      CompareAtLeast(sel_expr, range->index, aig, width, is_signed);
  uint32_t at_most =
      CompareAtLeast(range->index_end, sel_expr, aig, width, is_signed);
  propagated_signed_ = saved_signed;
  return aig.AddAnd(at_least, at_most);
}

void SynthLower::ReportWildcardUnlowered(const Expr* expr) {
  lowering_incomplete_ = true;
  std::string op =
      expr->op == TokenKind::kEqEqQuestion ? "'a ==? b'" : "'a !=? b'";
  diag_.Error(expr->range.start,
              op + " with a right operand that is not an integer literal has no"
                   " lowering in the synthesizer",
              Subclause("11.4.6"));
}

uint32_t SynthLower::LowerWildcardMatch(const Expr* expr, AigGraph& aig) {
  const Expr* pat = expr->rhs;
  if (pat->kind != ExprKind::kIntegerLiteral) {
    ReportWildcardUnlowered(expr);
    return AigGraph::kConstFalse;
  }
  uint32_t width = CompareWidth(expr->lhs, pat);
  if (pat->text.find('\'') == std::string_view::npos) {
    return CompareEqual(expr->lhs, pat, aig, width, false);
  }
  LowerCtx ctx{aig, *this};
  return BuildPatternMatch(expr->lhs, pat, ctx, width, TokenKind::kKwCasex);
}

uint32_t SynthLower::LowerCompareMatch(const Expr* expr, AigGraph& aig) {
  if (ComparesWithWildcards(expr->op)) return LowerWildcardMatch(expr, aig);

  const Expr* lhs = expr->lhs;
  const Expr* rhs = expr->rhs;
  if (ComparesExchangedOperands(expr->op)) std::swap(lhs, rhs);

  uint32_t width = CompareWidth(lhs, rhs);
  bool is_signed = IsSignedExpr(lhs) && IsSignedExpr(rhs);
  if (ComparesForEquality(expr->op)) {
    return CompareEqual(lhs, rhs, aig, width, is_signed);
  }
  return CompareAtLeast(lhs, rhs, aig, width, is_signed);
}

uint32_t SynthLower::LowerCompareBit(const Expr* expr, AigGraph& aig,
                                     uint32_t bit) {
  if (bit > 0) return AigGraph::kConstFalse;
  uint32_t saved_width = propagated_width_;
  bool saved_signed = propagated_signed_;
  propagated_width_ = std::max(ExprWidth(expr->lhs).value_or(0),
                               ExprWidth(expr->rhs).value_or(0));
  propagated_signed_ = IsSignedExpr(expr->lhs) && IsSignedExpr(expr->rhs);
  uint32_t match = LowerCompareMatch(expr, aig);
  propagated_width_ = saved_width;
  propagated_signed_ = saved_signed;
  if (ComparesNegated(expr->op)) return aig.AddNot(match);
  return match;
}

static std::vector<const Expr*> CaseItemOperands(const Stmt* stmt) {
  std::vector<const Expr*> operands;
  for (const auto& ci : stmt->case_items) {
    for (const auto* pat : ci.patterns) {
      if (pat->kind == ExprKind::kSelect && pat->base == nullptr) {
        operands.push_back(pat->index);
        operands.push_back(pat->index_end);
      } else {
        operands.push_back(pat);
      }
    }
  }
  return operands;
}

std::optional<uint32_t> SynthLower::CaseCompareWidth(const Stmt* stmt) {
  std::optional<uint32_t> width = ExprWidth(stmt->condition);
  if (!width) return std::nullopt;
  for (const auto* operand : CaseItemOperands(stmt)) {
    width = std::max(*width, ExprWidth(operand).value_or(0));
  }
  return width;
}

bool SynthLower::IsSignedCase(const Stmt* stmt) {
  if (!IsSignedExpr(stmt->condition)) return false;
  for (const auto* operand : CaseItemOperands(stmt)) {
    if (!IsSignedExpr(operand)) return false;
  }
  return true;
}

std::optional<bool> SynthLower::TypeRefCompareHere(const Expr* expr) const {
  if (type_ref_compares_ == nullptr) return std::nullopt;
  for (const TypeRefCompareResult& result : *type_ref_compares_) {
    if (result.expr == expr && result.gen_prefix == gen_prefix_) {
      return result.holds;
    }
  }
  return std::nullopt;
}

}  // namespace delta
