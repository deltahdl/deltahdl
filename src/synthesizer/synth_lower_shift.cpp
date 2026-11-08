#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

namespace delta {

bool IsShiftOp(TokenKind op) {
  switch (op) {
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return true;
    default:
      return false;
  }
}

static bool ShiftsLeft(TokenKind op) {
  return op == TokenKind::kLtLt || op == TokenKind::kLtLtLt;
}

struct ShiftRule {
  bool moves_left;
  uint32_t vacated;
};

static ShiftRule ShiftRuleFor(TokenKind op, bool result_signed,
                              uint32_t sign_bit) {
  bool fills_with_sign_bit = op == TokenKind::kGtGtGt && result_signed;
  uint32_t vacated = fills_with_sign_bit ? sign_bit : AigGraph::kConstFalse;
  return ShiftRule{ShiftsLeft(op), vacated};
}

static constexpr uint32_t kShiftAmountBits = 64;

static std::vector<uint32_t> ShiftStage(const std::vector<uint32_t>& bits,
                                        AigGraph& aig, uint32_t sel,
                                        size_t amount, ShiftRule rule) {
  size_t width = bits.size();
  std::vector<uint32_t> moved(width);
  for (size_t b = 0; b < width; ++b) {
    uint32_t source = rule.vacated;
    if (rule.moves_left) {
      if (amount <= b) source = bits[b - amount];
    } else if (amount < width - b) {
      source = bits[b + amount];
    }
    moved[b] = aig.AddMux(sel, source, bits[b]);
  }
  return moved;
}

uint32_t SynthLower::ShiftWidth(const Expr* lhs) {
  return std::max(propagated_width_, SignalWidth(lhs->text));
}

uint32_t SynthLower::LowerShiftBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit) {
  uint32_t width = ShiftWidth(expr->lhs);
  if (bit >= width) return AigGraph::kConstFalse;

  bool result_signed = propagated_signed_;

  std::vector<uint32_t> bits(width);
  for (uint32_t b = 0; b < width; ++b) {
    bits[b] = LowerExtendedOperandBit(expr->lhs, aig, b, result_signed);
  }
  ShiftRule rule = ShiftRuleFor(expr->op, result_signed, bits[width - 1]);

  uint32_t beyond = AigGraph::kConstFalse;
  for (uint32_t stage = 0; stage < kShiftAmountBits; ++stage) {
    uint32_t sel = LowerExprBit(expr->rhs, aig, stage);
    uint64_t amount = uint64_t{1} << stage;
    if (amount >= width) {
      beyond = aig.AddOr(beyond, sel);
      continue;
    }
    bits = ShiftStage(bits, aig, sel, static_cast<size_t>(amount), rule);
  }

  return aig.AddMux(beyond, rule.vacated, bits[bit]);
}

}  // namespace delta
