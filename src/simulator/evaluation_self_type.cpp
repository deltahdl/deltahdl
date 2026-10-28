// §11.6.1 and §11.8.1: the self-determined length and signedness of an
// expression as its form gives them, which the context-determined evaluators
// in evaluation.cpp and eval_ternary.cpp size and sign their operands by
// (§11.8.2), by the classes of operator elaborator/operator_classes.h names;
// and §11.3.4's 2- or 4-state nature of it, which a cast to a type reference
// (§6.23) takes.

#include <algorithm>
#include <cstdint>

#include "elaborator/operator_classes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

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
      return var == nullptr || var->is_signed || var->is_real;
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
      return var != nullptr && var->is_real;
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

// §11.3.4: whether an expression's self-determined type is 4-state, as its
// form says. An operator applied to 2-state operands only gives a 2-state
// result, so a name is 4-state by its declared type, an operator and a
// conditional where any operand they read is, the condition included, and any
// other form, a literal among them, is 4-state.
bool SimSelf4State(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var == nullptr || var->is_4state;
    }
    case ExprKind::kUnary:
      return SimSelf4State(expr->lhs, ctx);
    case ExprKind::kBinary:
      return SimSelf4State(expr->lhs, ctx) || SimSelf4State(expr->rhs, ctx);
    case ExprKind::kTernary:
      return SimSelf4State(expr->condition, ctx) ||
             SimSelf4State(expr->true_expr, ctx) ||
             SimSelf4State(expr->false_expr, ctx);
    default:
      return true;
  }
}

}  // namespace delta
