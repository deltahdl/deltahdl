// §11.6.1 and §11.8.1: the self-determined length and signedness of an
// expression as its form gives them, which the context-determined evaluators
// in evaluation.cpp and eval_ternary.cpp size and sign their operands by
// (§11.8.2), and the classes of operator the two rules name.

#include <algorithm>
#include <cstdint>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §11.6.1 Table 11-21: arithmetic and bitwise operators whose result width is
// the maximum width of the two operands; both operands are context-determined.
bool IsMaxWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

// §11.6.1: shift and power operators whose result width is the left operand's
// width; the left operand is context-determined, the right self-determined.
bool IsLeftWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPower:
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return true;
    default:
      return false;
  }
}

bool IsUnaryReductionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

// §11.6.1: the self-determined bit length of an expression, resolving variable
// widths through the simulation context. Returns 0 ("indeterminate") for node
// kinds whose width cannot be derived structurally (selects, member access,
// calls, casts, ...); callers treat 0 as "do not force-widen", so such an
// operand keeps its own evaluated width and the result is left unchanged.
uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return LiteralWidth(expr->text, expr->int_val);
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;  // §5.7.1: one bit where self-determined
    case ExprKind::kIdentifier: {
      auto* var = ctx.FindVariable(expr->text);
      return var ? var->value.width : 0;
    }
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kBang || IsUnaryReductionOp(expr->op))
        return 1;
      return SimSelfWidth(expr->lhs, ctx);
    case ExprKind::kBinary:
      if (IsMaxWidthBinaryOp(expr->op))
        return std::max(SimSelfWidth(expr->lhs, ctx),
                        SimSelfWidth(expr->rhs, ctx));
      if (IsLeftWidthBinaryOp(expr->op)) return SimSelfWidth(expr->lhs, ctx);
      return 1;  // comparison / equality / logical -> one-bit result
    case ExprKind::kTernary:
      return std::max(SimSelfWidth(expr->true_expr, ctx),
                      SimSelfWidth(expr->false_expr, ctx));
    default:
      return 0;
  }
}

// §11.8.1: whether an expression's self-determined type is signed, as far as
// its form says. A literal is signed by its base, a name by its declared type,
// an arithmetic or bitwise operator where both its operands are, a unary
// operator and a shift or power by the operand they size from, and a
// conditional where both its results are. A comparison, a logical operator, a
// reduction and a concatenation are unsigned. A form this does not read, and a
// real value, answer signed, which leaves the operand's own sign to decide.
bool SimSelfSigned(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return IsSignedLiteral(expr->text);
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var == nullptr || var->value.is_signed || var->value.is_real;
    }
    case ExprKind::kUnary:
      return expr->op != TokenKind::kBang && !IsUnaryReductionOp(expr->op) &&
             SimSelfSigned(expr->lhs, ctx);
    case ExprKind::kBinary:
      if (IsMaxWidthBinaryOp(expr->op))
        return SimSelfSigned(expr->lhs, ctx) && SimSelfSigned(expr->rhs, ctx);
      return IsLeftWidthBinaryOp(expr->op) && SimSelfSigned(expr->lhs, ctx);
    case ExprKind::kTernary:
      return SimSelfSigned(expr->true_expr, ctx) &&
             SimSelfSigned(expr->false_expr, ctx);
    case ExprKind::kConcatenation:
      return false;
    default:
      return true;
  }
}

// §11.4.11 with §6.12: whether an expression's self-determined type is real,
// as its form says: a real or time literal, a real variable, and an operator
// one of whose operands it takes its type from is.
bool SimSelfReal(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var != nullptr && var->value.is_real;
    }
    case ExprKind::kBinary:
      return IsMaxWidthBinaryOp(expr->op) &&
             (SimSelfReal(expr->lhs, ctx) || SimSelfReal(expr->rhs, ctx));
    case ExprKind::kTernary:
      return SimSelfReal(expr->true_expr, ctx) ||
             SimSelfReal(expr->false_expr, ctx);
    default:
      return false;
  }
}

}  // namespace delta
