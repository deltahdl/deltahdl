// The width and type an expression propagates down to its operands. §11.6.1
// (printed pages 299-300 of IEEE 1800-2023) has the size of an expression
// determined by its operands and by the context it stands in -- in an
// assignment, the left-hand side counts among the operands -- and Table
// 11-21 says which operands are self-determined instead: a shift's count, a
// power's exponent, the parts of a concatenation and a replication, a
// condition, and the operands of a logical operator; a relational or an
// equality operator's operands are sized to each other and to nothing
// outside. §11.8.2 (printed 302-303) then orders an evaluation: the size and
// the type of the expression are determined, propagated back down to every
// context-determined operand, each simple operand reached is converted to
// them -- extended from its sign only where the propagated type is signed --
// and only then is the operator applied. §11.8.1 (printed 302) types the
// expression unsigned where any operand that is not self-determined is
// unsigned, and never by the left-hand side. The fold before this evaluated
// every operand at its own width and extended the value it got, so
// `localparam logic [95:0] X = 3 ** 50` raised 3 at the 32 bits of the
// literal, `localparam [15:0] Y = 8'hAB << 8` shifted at 8 bits and read 0,
// `localparam logic [63:0] Z = 32'hFFFF_FFFF + 1` carried out of 32 bits and
// read 0, and §11.6.2's own remedy `(a + b + 0) >> 1` (printed 300) added
// at the width of a and b.

#include <algorithm>
#include <cstdint>
#include <optional>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

// Table 11-21: the logical operators and the implications, every operand of
// which is self-determined, each read for being nonzero (§11.4.7).
bool OperandsSelfDetermined(TokenKind op) {
  switch (op) {
    case TokenKind::kAmpAmp:
    case TokenKind::kPipePipe:
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return true;
    default:
      return false;
  }
}

// Table 11-21: the relational and equality operators, whose operands are
// sized to the wider of the two (§11.8.2, printed 303) and whose answer is
// one bit.
bool OperandsSizedToEachOther(TokenKind op) {
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

// The context two operands share once both are folded: the wider width, and
// the unsigned type where either is unsigned (§11.8.1).
FoldContext SharedContext(const ConstVal& a, const ConstVal& b) {
  return {std::max(a.width, b.width), !(a.is_signed && b.is_signed)};
}

// Whether an operand that folded to `v` was folded outside `ctx`: narrower
// than the width it propagates, or signed where it reads unsigned. A simple
// operand reads the same either way once ReadInContext converts it; one that
// is itself an expression has to be folded again, its operator having been
// applied at a width and a type the expression has since changed (§11.8.2).
bool FoldedOutside(const ConstVal& v, FoldContext ctx) {
  return v.width < ctx.width || (v.is_signed && ctx.read_unsigned);
}

// The width a size or a type cast pads or truncates its operand to. §6.24.1:
// "If the casting type is a constant expression with a positive integral
// value, the expression in parentheses shall be padded or truncated to the
// size specified." The parser gives such a cast its size as an expression on
// rhs rather than as a name on text -- MakeNodeCast in
// src/parser/expr_parser.cpp builds `4'(x)` and `(W)'(x)` alike -- so the
// size is folded here in the same scope the operand is; empty for a size
// that does not fold or is not positive. A cast to a user-defined type takes
// its width from the typedef map, which ConstEvalFull is not given: a
// ScopeMap is its only other argument. CastTargetWidth answers 0 for such a
// name and for `string`, and the operand's own width and signedness then
// stand in, as InferCastWidth in src/elaborator/type_eval.cpp falls back to
// the operand's width for the same reason.
std::optional<uint32_t> CastWidth(const Expr* expr, const ScopeMap& scope) {
  if (expr->rhs == nullptr) return CastTargetWidth(expr->text);
  auto size = ConstEvalFull(expr->rhs, scope);
  if (!size || size->value <= 0) return std::nullopt;
  return static_cast<uint32_t>(size->value);
}

}  // namespace

bool AnswersOneBit(TokenKind op) {
  return OperandsSelfDetermined(op) || OperandsSizedToEachOther(op);
}

ConstVal ReadInContext(const ConstVal& v, FoldContext ctx) {
  uint32_t width = std::max(v.width, ctx.width);
  bool is_signed = v.is_signed && !ctx.read_unsigned;
  if (width == v.width && is_signed == v.is_signed) return v;
  return ConstValOfWords(ExtendedWords(v, width, is_signed), width, is_signed);
}

std::optional<BinaryOperands> FoldBinaryOperands(const Expr* expr,
                                                 const ScopeMap& scope,
                                                 FoldContext ctx) {
  const TokenKind kOp = expr->op;
  const bool kLeftOnly = SizedByLeftOperand(kOp);
  const bool kOneBit = AnswersOneBit(kOp);
  const FoldContext kLeftCtx = kOneBit ? FoldContext{} : ctx;
  const FoldContext kRightCtx = kOneBit || kLeftOnly ? FoldContext{} : ctx;
  auto lhs = ConstEvalFull(expr->lhs, scope, kLeftCtx);
  auto rhs = ConstEvalFull(expr->rhs, scope, kRightCtx);
  if (!lhs || !rhs) return std::nullopt;
  if (kLeftOnly || OperandsSelfDetermined(kOp))
    return BinaryOperands{*lhs, *rhs};
  const FoldContext kShared = SharedContext(*lhs, *rhs);
  if (FoldedOutside(*lhs, kShared))
    lhs = ConstEvalFull(expr->lhs, scope, kShared);
  if (FoldedOutside(*rhs, kShared))
    rhs = ConstEvalFull(expr->rhs, scope, kShared);
  if (!lhs || !rhs) return std::nullopt;
  return BinaryOperands{*lhs, *rhs};
}

// §6.24.1: what a cast expression is worth. Each form decides the width and the
// signedness the operand's bits are read by, which is what CastConstVal
// applies, keeping the words above bit 63 of an operand or a size past 64
// bits, which the NormalizeConstVal of 64b2dfbe0 dropped: a signing cast keeps
// "the number of bits in the expression to be cast" and sets "the signedness
// specified by the cast type"; a size cast takes "the cast size" and leaves
// "the self-determined signedness of the expression inside the cast" alone; a
// const cast lets "the type of the expression to be cast pass through
// unchanged"; a cast to a predefined type takes both from that type; and a
// void cast has no value to return.
std::optional<ConstVal> ConstEvalCastFull(const Expr* expr,
                                          const ScopeMap& scope) {
  if (expr->text == "void") return std::nullopt;
  const bool kKeepsWidth = expr->text == "const" || expr->text == "signed" ||
                           expr->text == "unsigned";
  std::optional<uint32_t> width =
      kKeepsWidth ? std::optional<uint32_t>{0} : CastWidth(expr, scope);
  if (!width) return std::nullopt;
  // §6.24.1 (printed page 139) has a cast return what a variable of the
  // casting type would hold after being assigned the expression, so the
  // expression is folded as the right-hand side of an assignment to a target
  // of the cast's width (§11.6.1) before it is cut to that width: `32'(8'd200
  // + 8'd100)` adds at 32 bits and holds 300. A signing or a const cast keeps
  // the operand's own width and folds it self-determined.
  auto operand = ConstEvalFull(expr->lhs, scope, FoldContext{*width});
  if (!operand) return std::nullopt;
  if (expr->text == "signed" || expr->text == "unsigned")
    return CastConstVal(*operand, operand->width, expr->text == "signed");
  if (expr->text == "const" || *width == 0) return operand;
  const bool kSizeCast =
      expr->rhs != nullptr || (expr->text[0] >= '0' && expr->text[0] <= '9');
  return CastConstVal(*operand, *width,
                      kSizeCast ? operand->is_signed
                                : TypeNameToDataType(expr->text).is_signed);
}

std::optional<ConstVal> ConstEvalTernaryFull(const Expr* expr,
                                             const ScopeMap& scope,
                                             FoldContext ctx) {
  auto cond = ConstEvalFull(expr->condition, scope);
  if (!cond) return std::nullopt;
  // §11.4.7 reads every bit of the condition, which the low word alone did
  // not for a condition wider than 64 bits.
  const Expr* arm =
      ConstValIsNonZero(*cond) ? expr->true_expr : expr->false_expr;
  return ConstEvalFull(arm, scope, ctx);
}

}  // namespace delta
