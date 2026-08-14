#include <algorithm>
#include <cstdint>
#include <vector>

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

// True for the two §11.4.10 left shift operators, `<<` and `<<<`, which shift
// their left operand to the left by the number of bit positions the right
// operand gives. False for the two right shift operators, `>>` and `>>>`,
// which shift it to the right by that number.
static bool ShiftsLeft(TokenKind op) {
  return op == TokenKind::kLtLt || op == TokenKind::kLtLtLt;
}

// What §11.4.10 decides about a shift operator before any operand is read: the
// direction it moves the left operand, and the value it fills the vacated bit
// positions with.
struct ShiftRule {
  bool moves_left;
  uint32_t vacated;
};

// The rule §11.4.10 gives one operator, over a result whose signedness and sign
// bit have already been read off the left operand.
static ShiftRule ShiftRuleFor(TokenKind op, bool result_signed,
                              uint32_t sign_bit) {
  // §11.4.10 fills the vacated bit positions with the most significant (i.e.,
  // sign) bit of the left operand for the arithmetic right shift `>>>` over a
  // signed result. Every other case fills them with zeros: both left shifts
  // fill with zeros whatever the result type is, the logical right shift `>>`
  // fills with zeros, and `>>>` fills with zeros where the result type is
  // unsigned.
  bool fills_with_sign_bit = op == TokenKind::kGtGtGt && result_signed;
  uint32_t vacated = fills_with_sign_bit ? sign_bit : AigGraph::kConstFalse;
  return ShiftRule{ShiftsLeft(op), vacated};
}

// A shift amount's value is held in the 64 bits of Expr::int_val, so the right
// operand is read at every position below that and at none above it.
static constexpr uint32_t kShiftAmountBits = 64;

// One stage of the shift: answer the operand bits as they stand where `sel` is
// false, and as they stand moved by `amount` positions where `sel` is true.
//
// AigGraph::AddMux folds a constant selector, so a stage whose bit of the right
// operand is a literal costs no gate and hands back one of its two inputs
// whole. That is what makes a shift by a written amount free: bit `b` of
// `a << k` is bit `b - k` of `a` and nothing else.
static std::vector<uint32_t> ShiftStage(const std::vector<uint32_t>& bits,
                                        AigGraph& aig, uint32_t sel,
                                        size_t amount, ShiftRule rule) {
  size_t width = bits.size();
  std::vector<uint32_t> moved(width);
  for (size_t b = 0; b < width; ++b) {
    // A position the move leaves no operand bit for is vacated, and §11.4.10
    // fills it with ShiftRule::vacated.
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
  // §11.6.1 Table 11-21 gives `i << j`, `i >> j`, `i <<< j` and `i >>> j` the
  // bit length L(i) and states that j is self-determined, which leaves the left
  // operand context-determined. §11.8.2 propagates the size of the expression
  // back down to a context-determined operand, so the shift is carried out over
  // the width SynthLower::propagated_width_ carries rather than over the width
  // the left operand was declared: `y` eight bits wide makes `y = a << 1` a
  // shift within eight positions, and the bit a four-bit `a` would have lost
  // off its top is kept.
  //
  // SynthLower::SignalWidth floors that at the left operand's own width, which
  // is what answers a shift lowered while no assignment has set
  // propagated_width_.
  return std::max(propagated_width_, SignalWidth(lhs->text));
}

uint32_t SynthLower::LowerShiftBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit) {
  uint32_t width = ShiftWidth(expr->lhs);
  if (bit >= width) return AigGraph::kConstFalse;

  // §11.4.10 rules that "The result signedness is determined by the left-hand
  // operand and the remainder of the expression, as outlined in 11.8.1", so the
  // type of the whole expression the shift stands in decides the fill and the
  // shift's own left operand does not: `(a >>> 1) | b` over an unsigned `b` is
  // unsigned however `a` was declared. §11.8.2 propagates that type back down
  // to the context-determined operands of the expression, and
  // SynthLower::propagated_signed_ is what carries it here.
  //
  // propagated_signed_ is read only where propagated_width_ says an assignment
  // is being lowered. A shift lowered anywhere else, such as in the condition
  // of an if statement, has no expression above it to propagate a type, and
  // §11.8.1 answers its type off its own operands.
  bool result_signed =
      propagated_width_ > 0 ? propagated_signed_ : IsSignedExpr(expr);

  // §11.8.2 rules that an operand the propagated size extends "shall be
  // sign-extended only if the propagated type is signed", which is the rule
  // SynthLower::LowerExtendedOperandBit carries.
  std::vector<uint32_t> bits(width);
  for (uint32_t b = 0; b < width; ++b) {
    bits[b] = LowerExtendedOperandBit(expr->lhs, aig, b, result_signed);
  }
  ShiftRule rule = ShiftRuleFor(expr->op, result_signed, bits[width - 1]);

  // Each stage moves the operand by one power of two, under the bit of the
  // right operand that stands for that power: stage i chooses between what the
  // stages below it produced and that same value moved by 2**i positions. The
  // stages below i have already moved the operand by the amount the right
  // operand's lower bits give, so running every stage in turn moves it by the
  // whole amount.
  //
  // The right operand's bits are read through SynthLower::LowerExprBit and are
  // never sign-extended, because §11.4.10 rules that the right operand is
  // always treated as an unsigned number. LowerExprBit answers constant false
  // above the operand's own width, so a stage above it moves nothing.
  //
  // A stage whose 2**i is at least the width leaves every bit position of the
  // result vacated, so it needs no muxes and only has to say whether the amount
  // reached that far. Those stages collapse into `beyond`, which the last mux
  // reads once.
  //
  // §11.4.10 also rules that a right operand with an x or z value makes the
  // result unknown, and nothing answers that here. An AigGraph node holds two
  // values, so no value a netlist here can carry is x or z, and no right
  // operand the graph can represent is unknown.
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

  // A shift by at least the width vacates every bit position of the result, so
  // §11.4.10 fills the whole result with ShiftRule::vacated.
  return aig.AddMux(beyond, rule.vacated, bits[bit]);
}

}  // namespace delta
