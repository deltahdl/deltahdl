#include <cstdint>
#include <optional>
#include <string>

#include "elaborator/type_eval.h"
#include "synthesizer/synth_lower.h"

namespace delta {

// The typedefs InferExprWidth resolves a named type against. The synthesizer
// lowers an already elaborated module, whose named types have been resolved
// into the widths its signals were recorded with, so nothing here has a
// typedef to add.
static const TypedefMap& NoTypedefs() {
  static const TypedefMap kNone;
  return kNone;
}

std::optional<uint32_t> SynthLower::ExprWidth(const Expr* expr) {
  if (!expr) return std::nullopt;
  switch (expr->kind) {
    case ExprKind::kIdentifier: {
      // InferExprWidth answers 0 for a name, because it reads the expression
      // and not the declaration. SynthLower recorded every declared width in
      // MapPorts, so the name is answered here.
      auto it = signal_widths_.find(expr->text);
      if (it == signal_widths_.end()) return std::nullopt;
      return it->second;
    }
    case ExprKind::kSelect: {
      // §11.5.1: a select is as wide as the run of bits it addresses.
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
    default: {
      uint32_t width = InferExprWidth(expr, NoTypedefs());
      if (width == 0) return std::nullopt;
      return width;
    }
  }
}

std::optional<uint32_t> SynthLower::ElementsWidth(const Expr* expr) {
  // §11.4.12: "the size of each operand in the concatenation is needed to
  // calculate the complete size of the concatenation", so one operand whose
  // width is unknown leaves the whole unknown.
  uint32_t total = 0;
  for (const auto* element : expr->elements) {
    std::optional<uint32_t> width = ExprWidth(element);
    if (!width) return std::nullopt;
    total += *width;
  }
  return total;
}

std::optional<uint32_t> SynthLower::ReplicateWidth(const Expr* expr) {
  // §11.4.12.1: the multiplier is a "non-negative, non-x, and non-z constant
  // expression", and the replication is that many copies of the concatenation
  // it multiplies.
  std::optional<int64_t> count = ConstEvalInt(expr->repeat_count, scope_);
  if (!count || *count < 0) return std::nullopt;
  std::optional<uint32_t> inner = ElementsWidth(expr);
  if (!inner) return std::nullopt;
  return static_cast<uint32_t>(*count) * *inner;
}

void SynthLower::ReportExprUnlowered(const Expr* expr, std::string_view message,
                                     Subclause subclause) {
  lowering_incomplete_ = true;
  // LowerContAssign and LowerAssignStmt ask for one bit at a time, so report
  // an expression only the first time it arrives.
  if (reported_exprs_.insert(expr).second) {
    diag_.Error(expr->range.start, std::string(message), subclause);
  }
}

uint32_t SynthLower::LowerElementsBit(const Expr* expr, AigGraph& aig,
                                      uint32_t bit) {
  // §11.4.12 gives the leftmost operand the most significant bits, which its
  // example states by reading `{a, b[3:0], w, 3'b101}` as `{a, b[3], b[2],
  // b[1], b[0], w, 1'b1, 1'b0, 1'b1}`. The operands are therefore walked from
  // the last one written to the first, each covering the run of result bits
  // its own width spans above the operands after it.
  uint32_t offset = 0;
  for (auto it = expr->elements.rbegin(); it != expr->elements.rend(); ++it) {
    uint32_t width = ExprWidth(*it).value_or(0);
    if (bit < offset + width) return LowerExprBit(*it, aig, bit - offset);
    offset += width;
  }
  // A bit at or above the width of the whole concatenation carries nothing the
  // design wrote, and §10.7 zero-fills a right-hand side narrower than its
  // target.
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

  // §11.4.12.1: the copies are identical, so the bit of the replication at
  // `bit` is the bit of the concatenation being replicated at `bit` modulo its
  // width. A multiplier of zero gives a width of zero, which the subclause
  // rules "is considered to have a size of zero and is ignored", and every bit
  // is answered above.
  uint32_t inner = ElementsWidth(expr).value_or(0);
  if (inner == 0) return AigGraph::kConstFalse;
  return LowerElementsBit(expr, aig, bit % inner);
}

}  // namespace delta
