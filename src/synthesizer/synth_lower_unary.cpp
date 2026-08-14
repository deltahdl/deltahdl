#include <cstdint>
#include <optional>

#include "synthesizer/synth_lower.h"

namespace delta {

// The operator §11.4.9 folds across the bits of the operand, and whether the
// fold is inverted afterwards. §11.4.9 defines the six reduction operators as
// three folds and their complements: "For reduction NAND, reduction NOR, and
// reduction XNOR operators, the result shall be computed by inverting the
// result of the reduction AND, reduction OR, and reduction XOR operation,
// respectively". `folded` is kEof for an operator that is not one of the six.
struct ReductionRule {
  TokenKind folded = TokenKind::kEof;
  bool invert = false;
};

// Table 11-1 of §11.3 lists `~^` and `^~` as one operator, and the lexer gives
// each spelling its own token, so both name the reduction XNOR here.
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

// One step of the fold, over the logic table §11.4.9 names for the operator:
// Table 11-16 for the reduction AND, Table 11-17 for the reduction OR and
// Table 11-18 for the reduction exclusive OR.
static uint32_t ReductionStep(AigGraph& aig, TokenKind folded, uint32_t left,
                              uint32_t right) {
  if (folded == TokenKind::kAmp) return aig.AddAnd(left, right);
  if (folded == TokenKind::kPipe) return aig.AddOr(left, right);
  return aig.AddXor(left, right);
}

uint32_t SynthLower::LowerReductionBit(const Expr* expr, AigGraph& aig,
                                       uint32_t bit) {
  // §11.4.9: the reduction operators "perform a bitwise operation on a single
  // operand to produce a single-bit result", so the result stands at bit 0 and
  // every bit above it is zero.
  if (bit > 0) return AigGraph::kConstFalse;

  // The fold runs over the bits of the operand, so an operand whose width the
  // synthesizer cannot answer is one it cannot fold over. Folding over a
  // guessed width answers a different function: a reduction AND folded over
  // positions above the operand takes in the zeros those positions read as and
  // is constant zero whatever the operand carries.
  std::optional<uint32_t> width = ExprWidth(expr->lhs);
  if (!width) {
    ReportExprUnlowered(expr,
                        "reduction operand has no width in the synthesizer, "
                        "so the reduction has no lowering",
                        Subclause("11.4.9"));
    return AigGraph::kConstFalse;
  }

  // §11.4.9: "the first step of the operation shall apply the operator between
  // the first bit of the operand and the second", and "The second and
  // subsequent steps shall apply the operator between the 1-bit result of the
  // prior step and the next bit of the operand".
  ReductionRule rule = ReductionRuleFor(expr->op);
  uint32_t result = LowerExprBit(expr->lhs, aig, 0);
  for (uint32_t b = 1; b < *width; ++b) {
    result = ReductionStep(aig, rule.folded, result,
                           LowerExprBit(expr->lhs, aig, b));
  }
  return rule.invert ? aig.AddNot(result) : result;
}

uint32_t SynthLower::LowerNegateBit(const Expr* expr, AigGraph& aig,
                                    uint32_t bit) {
  // Table 11-6 of §11.4.3 gives `-m` as "Unary minus m", and §11.4.3.1 rules
  // that a signed value "shall use a two's-complement representation", which
  // makes the negation the complement of the operand plus one. Bit `bit` of
  // that sum depends on every bit of the operand below it, so the chain is
  // rippled from bit 0 up rather than the operand read at `bit` alone.
  uint32_t carry = AigGraph::kConstTrue;
  uint32_t sum = AigGraph::kConstFalse;
  for (uint32_t b = 0; b <= bit; ++b) {
    uint32_t complemented = aig.AddNot(LowerExprBit(expr->lhs, aig, b));
    sum = FullAdderBit(aig, AigGraph::kConstFalse, complemented, carry);
  }
  return sum;
}

uint32_t SynthLower::LowerUnaryBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit) {
  if (expr->op == TokenKind::kTilde) {
    // Table 11-15 of §11.4.8 gives the bitwise negation one result per bit.
    return aig.AddNot(LowerExprBit(expr->lhs, aig, bit));
  }
  if (expr->op == TokenKind::kBang) {
    // §11.4.7 states the result of the logical negation as `1'b0` or `1'b1`.
    if (bit > 0) return AigGraph::kConstFalse;
    return aig.AddNot(LowerExprBit(expr->lhs, aig, 0));
  }
  if (expr->op == TokenKind::kPlus) {
    // Table 11-6 of §11.4.3: "Unary plus m (same as m)".
    return LowerExprBit(expr->lhs, aig, bit);
  }
  if (expr->op == TokenKind::kMinus) return LowerNegateBit(expr, aig, bit);
  if (ReductionRuleFor(expr->op).folded != TokenKind::kEof) {
    return LowerReductionBit(expr, aig, bit);
  }

  // Every operator Parser::PrefixBp in src/parser/expr_parser.cpp accepts is
  // answered above, so what reaches here is a unary expression built somewhere
  // else, such as the `++i` and `--i` of §11.4.2 written inside an expression
  // rather than as a statement. Answering the operand at `bit` is what this
  // function used to do for all of them, and that is a netlist computing a
  // different function than the design wrote. No subclause states this: it is a
  // limit of this synthesizer rather than a rule the design broke.
  ReportExprUnlowered(
      expr,
      "unary operator has no lowering in the synthesizer and would be "
      "dropped from the netlist",
      Subclause::None());
  return AigGraph::kConstFalse;
}

}  // namespace delta
