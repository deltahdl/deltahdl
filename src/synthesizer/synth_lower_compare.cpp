#include <algorithm>
#include <string>
#include <string_view>
#include <utility>

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

// True for the two §11.4.4 operators Table 11-8 states by exchanging the
// operands of another of the four: `a > b` holds exactly where `b < a` does,
// and `a <= b` exactly where `b >= a` does. Both are therefore answered by
// comparing the operands in the other order.
static bool ComparesExchangedOperands(TokenKind op) {
  return op == TokenKind::kGt || op == TokenKind::kLtEq;
}

// True for the five comparison operators that answer the negation of another of
// the ten. Table 11-8 makes `a < b` false exactly where `a >= b` is true and
// `a > b` false exactly where `a <= b` is true, and Table 11-9 and Table 11-10
// make each inequality the negation of the equality beside it.
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

// True for the four §11.4.5 equality operators, which compare their operands
// bit for bit, and false for the four §11.4.4 relational operators, which
// compare their magnitudes.
//
// `a === b` is here beside `a == b`, and `a !== b` beside `a != b`. §11.4.5
// rules that the case equality operators include the x and z bits of both
// operands in the comparison and always answer a known value, while the logical
// ones answer 1'bx when an x or z leaves the relation ambiguous. An AigGraph
// node holds two values, so no value a netlist here can carry is x or z, no
// relation over one is ambiguous, and the two operators are the same function
// of every operand pair the graph can represent.
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

// True for the two §11.4.6 wildcard equality operators, whose right operand
// carries the bit positions the comparison leaves out.
static bool ComparesWithWildcards(TokenKind op) {
  return op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

// An integer literal's value is held in the 64 bits of Expr::int_val, so a
// comparison against one is carried out over at least that many positions.
static constexpr uint32_t kLiteralBits = 64;

uint32_t SynthLower::CompareWidth(const Expr* lhs, const Expr* rhs) {
  // §11.4.4 and §11.4.5 rule that the smaller operand is extended to the size
  // of the larger, which makes the wider of the two the width to compare over.
  // Comparing over more positions than either operand declares answers the
  // same, because both operands are extended into those positions by the rule
  // the two subclauses give: their extension bits are equal wherever the values
  // are equal, and they order the operands as the operands themselves are
  // ordered wherever they are not.
  //
  // SynthLower::SignalWidth answers 1 for a name it holds no width for, which
  // is every operand that is not a signal, so a literal and a nested expression
  // contribute nothing above the floor kLiteralBits sets.
  return std::max(kLiteralBits,
                  std::max(SignalWidth(lhs->text), SignalWidth(rhs->text)));
}

uint32_t SynthLower::LowerExtendedOperandBit(const Expr* expr, AigGraph& aig,
                                             uint32_t bit, bool sign_extend) {
  // §11.8.2 rules that an operand the propagated size extends "shall be
  // sign-extended only if the propagated type is signed", so `sign_extend` is
  // what decides the positions above the operand's own width. They carry zero
  // otherwise, which is what SynthLower::GetSignalBit already answers above a
  // signal's own width.
  //
  // §11.4.4 and §11.4.5 set `sign_extend` from both operands of a comparison
  // being signed, since either one unsigned makes it a comparison between
  // unsigned values. §11.4.10 sets it from the left operand of a shift alone.
  uint32_t width = SignalWidth(expr->text);
  if (sign_extend && bit >= width) return GetSignalBit(expr->text, width - 1);
  return LowerExprBit(expr, aig, bit);
}

uint32_t SynthLower::CompareEqual(const Expr* lhs, const Expr* rhs,
                                  AigGraph& aig, uint32_t width,
                                  bool is_signed) {
  // §11.4.5: the operands are equal exactly where no bit position differs, and
  // a bit position differs exactly where AigGraph::AddXor of the two bits is
  // true.
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
  // §11.4.4 answers `a >= b` with the carry out of `a + ~b + 1`, which is the
  // subtraction §11.4.3 defines: the chain runs off its top stage carrying one
  // exactly where the subtraction did not borrow, and it borrows exactly where
  // the left operand is the smaller. The stage is the one
  // SynthLower::LowerAddSubBit builds a subtraction from rather than a second
  // chain written for the comparison, and AigGraph::AddAnd hands back the node
  // it already built for a pair of literals, so `a - b` and `a >= b` over the
  // same operands share the chain. Only the carry answers the comparison; the
  // sum each stage returns is what the subtraction reads and this does not.
  //
  // A signed comparison is that chain with the top bit of each operand
  // complemented. §11.4.4 rules that both operands signed makes the expression
  // a comparison between signed values, and complementing the sign bit adds
  // 2**(width-1) to each operand, which leaves the two in the order the signed
  // values are in rather than the order their bit patterns are in.
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

void SynthLower::ReportWildcardUnlowered(const Expr* expr) {
  // §11.4.6 rules that the x and z values of the right operand act as
  // wildcards, and the digits of a literal are the only place this synthesizer
  // can read which positions those are: an AigGraph node holds two values and
  // neither of them is x or z, so a signal arrives with no wildcard on it. The
  // lowering is marked incomplete so that SynthLower::Lower answers no netlist,
  // rather than one whose bits stand for a comparison it never built.
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
  // A literal written with no base is decimal digits alone, so it holds no x, z
  // or ? for §11.4.6 to make a wildcard of and what is left of the operator is
  // the §11.4.5 comparison of the two operands. BuildPatternMatch reads the
  // wildcard positions out of the digits that follow the base, and answers a
  // value of zero for a literal that carries no base at all, which would
  // compare the left operand against zero rather than against the literal.
  if (pat->text.find('\'') == std::string_view::npos) {
    return CompareEqual(expr->lhs, pat, aig, width, false);
  }
  // §11.4.6 makes both x and z in the right operand wildcards, which is what
  // §12.5.1 casex does to a case item's pattern, so the match is the one
  // SynthLower::LowerCaseStmt asks for over a casex item.
  LowerCtx ctx{aig, *this};
  return BuildPatternMatch(expr->lhs, pat, ctx, width, TokenKind::kKwCasex);
}

uint32_t SynthLower::LowerCompareMatch(const Expr* expr, AigGraph& aig) {
  if (ComparesWithWildcards(expr->op)) return LowerWildcardMatch(expr, aig);

  const Expr* lhs = expr->lhs;
  const Expr* rhs = expr->rhs;
  if (ComparesExchangedOperands(expr->op)) std::swap(lhs, rhs);

  uint32_t width = CompareWidth(lhs, rhs);
  // §11.4.4 and §11.4.5 both rule that one unsigned operand makes the whole
  // comparison unsigned, so a signed comparison is one both operands are signed
  // for. SynthLower::IsSignedSignal answers false for a name it holds no
  // signedness for, which is every operand that is not a signal.
  bool is_signed = IsSignedSignal(lhs->text) && IsSignedSignal(rhs->text);
  if (ComparesForEquality(expr->op)) {
    return CompareEqual(lhs, rhs, aig, width, is_signed);
  }
  return CompareAtLeast(lhs, rhs, aig, width, is_signed);
}

uint32_t SynthLower::LowerCompareBit(const Expr* expr, AigGraph& aig,
                                     uint32_t bit) {
  // §11.4.4 rules that a relational expression yields 1'b0 or 1'b1, §11.4.5
  // rules the same for the equality operators, and §11.4.6 makes a wildcard
  // comparison a 1-bit self-determined result, so the comparison occupies bit 0
  // and every bit of the target above it is zero. SynthLower::LowerBinaryBit
  // already has that shape for the §11.4.7 logical operators.
  if (bit > 0) return AigGraph::kConstFalse;
  uint32_t match = LowerCompareMatch(expr, aig);
  if (ComparesNegated(expr->op)) return aig.AddNot(match);
  return match;
}

}  // namespace delta
