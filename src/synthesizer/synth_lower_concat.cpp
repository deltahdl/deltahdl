#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static const TypedefMap& NoTypedefs() {
  static const TypedefMap kNone;
  return kNone;
}

static std::optional<uint32_t> LongerOf(std::optional<uint32_t> a,
                                        std::optional<uint32_t> b) {
  if (!a || !b) return std::nullopt;
  return std::max(*a, *b);
}

std::optional<uint32_t> SynthLower::ExprWidth(const Expr* expr) {
  if (!expr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kIdentifier: {
      auto it = signal_widths_.find(expr->text);
      if (it == signal_widths_.end()) return std::nullopt;
      return it->second;
    }
    case ExprKind::kSelect: {
      SelectStorage storage = ResolveSelect(expr);
      if (storage.count > 0) return storage.count;
      int64_t width = VariableSelectWidth(expr);
      if (width <= 0) return std::nullopt;
      return static_cast<uint32_t>(width);
    }
    case ExprKind::kConcatenation:
      return ElementsWidth(expr);
    case ExprKind::kReplicate:
      return ReplicateWidth(expr);
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kTernary:
      return OperatorWidth(expr);
    default: {
      uint32_t width = InferExprWidth(expr, NoTypedefs());
      if (width == 0) return std::nullopt;
      return width;
    }
  }
}

std::optional<uint32_t> SynthLower::OperatorWidth(const Expr* expr) {
  if (expr->kind == ExprKind::kUnary) {
    if (IsUnsignedResultUnaryOp(expr->op)) return 1;
    return ExprWidth(expr->lhs);
  }
  if (expr->kind == ExprKind::kTernary) {
    return LongerOf(ExprWidth(expr->true_expr), ExprWidth(expr->false_expr));
  }
  if (IsCompareOp(expr->op) || IsLogicalOp(expr->op)) return 1;
  if (IsShiftOp(expr->op) || expr->op == TokenKind::kPower) {
    return ExprWidth(expr->lhs);
  }
  return LongerOf(ExprWidth(expr->lhs), ExprWidth(expr->rhs));
}

std::optional<uint32_t> SynthLower::ElementsWidth(const Expr* expr) {
  uint32_t total = 0;
  for (const auto* element : expr->elements) {
    std::optional<uint32_t> width = ExprWidth(element);
    if (!width) return std::nullopt;
    total += *width;
  }
  return total;
}

std::optional<uint32_t> SynthLower::ReplicateWidth(const Expr* expr) {
  std::optional<int64_t> count = ConstEvalInt(expr->repeat_count, scope_);
  if (!count || *count < 0) return std::nullopt;
  std::optional<uint32_t> inner = ElementsWidth(expr);
  if (!inner) return std::nullopt;
  return static_cast<uint32_t>(*count) * *inner;
}

void SynthLower::ReportExprUnlowered(const Expr* expr, std::string_view message,
                                     Subclause subclause) {
  lowering_incomplete_ = true;
  if (reported_exprs_.insert(expr).second) {
    diag_.Error(expr->range.start, std::string(message), subclause);
  }
}

void SynthLower::ReportUnloweredTarget(const Expr* target) {
  ReportExprUnlowered(target,
                      "assignment target has no lowering in the synthesizer "
                      "and would be dropped from the netlist",
                      Subclause::None());
}

uint32_t SynthLower::LowerElementsBit(const Expr* expr, AigGraph& aig,
                                      uint32_t bit) {
  uint32_t offset = 0;
  for (auto it = expr->elements.rbegin(); it != expr->elements.rend(); ++it) {
    uint32_t width = ExprWidth(*it).value_or(0);
    if (bit < offset + width) {
      uint32_t saved_width = propagated_width_;
      bool saved_signed = propagated_signed_;
      propagated_width_ = width;
      propagated_signed_ = IsSignedExpr(*it);
      uint32_t lit = LowerExprBit(*it, aig, bit - offset);
      propagated_width_ = saved_width;
      propagated_signed_ = saved_signed;
      return lit;
    }
    offset += width;
  }
  return AigGraph::kConstFalse;
}

uint32_t SynthLower::LowerConcatBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  if (!ElementsWidth(expr)) {
    ReportExprUnlowered(expr,
                        "concatenation operand has no width in the "
                        "synthesizer, so the concatenation has no lowering",
                        Subclause("11.4.12"));
    return AigGraph::kConstFalse;
  }
  return LowerElementsBit(expr, aig, bit);
}

uint32_t SynthLower::LowerReplicateBit(const Expr* expr, AigGraph& aig,
                                       uint32_t bit) {
  std::optional<uint32_t> width = ReplicateWidth(expr);
  if (!width) {
    ReportExprUnlowered(expr,
                        "replication has no lowering in the synthesizer, "
                        "because its multiplier did not fold to a constant or "
                        "an operand of it has no width",
                        Subclause("11.4.12.1"));
    return AigGraph::kConstFalse;
  }
  if (bit >= *width) return AigGraph::kConstFalse;

  uint32_t inner = ElementsWidth(expr).value_or(0);
  if (inner == 0) return AigGraph::kConstFalse;
  return LowerElementsBit(expr, aig, bit % inner);
}

}  // namespace delta
