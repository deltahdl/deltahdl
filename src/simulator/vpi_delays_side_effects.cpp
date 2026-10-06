#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// §37.3.4 and §37.3.5: which objects carry a delay written in the source and
// which expressions have side effects. They sit in a file of their own because
// the value routines of vpi_value.cpp they were written beside had grown to the
// length .github/workflows/deltahdl.yml admits a source file.

namespace delta {

// ===========================================================================
// §37.3.4 Delays and values.
// ===========================================================================

bool VpiObjectCarriesSourceDelay(int type) {
  // §37.3.4: the object kinds that can carry a delay written within the
  // SystemVerilog source - nets, primitives, module paths, timing checks, and
  // continuous assignments. A primitive here covers the gate, switch, and udp
  // forms
  // as well as the primitive supertype. Other delays (module input port delays,
  // inter-module path delays) do not appear in the source and so are excluded.
  switch (type) {
    case vpiNet:
    case vpiPrimitive:
    case vpiGate:
    case vpiSwitch:
    case vpiUdp:
    case vpiModPath:
    case vpiTchk:
    case vpiContAssign:
    // §37.47 (figure): the vpiDelay edge is drawn on the unnamed enclosure that
    // holds the continuous assignment and its bits alike, so a cont assign bit
    // reaches the same source-written delay its assignment does.
    case vpiContAssignBit:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiSourceDelayExpr(VpiHandle obj) {
  // §37.3.4: the vpiDelay relation reaches the source-specified delay
  // expression of a delay-carrying object. It is a designated expression, not a
  // child found by type (a single delay is a plain constant-valued expression),
  // so it is held on the object directly. Null when the handle is null, is not
  // a delay-carrying kind, or carries no source delay.
  if (!obj) return nullptr;
  if (!VpiObjectCarriesSourceDelay(obj->type)) return nullptr;
  return obj->delay_expr;
}

bool VpiSourceDelayExprIsListOp(VpiHandle expr) {
  // §37.3.4: when more than one delay is specified the vpiDelay expression
  // shall be an operation whose vpiOpType is vpiListOp; a single delay is a
  // plain constant-valued expression instead. This holds iff the expression is
  // that operation form.
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

bool VpiExpressionHasSideEffects(const VpiObject* obj) {
  // §37.3.5: the mark records the classification described in the subclause; an
  // absent object cannot have side effects.
  return obj && obj->has_side_effects;
}

// §11.4.1 lists the assignment operators as the simple "=" together with "the C
// assignment operators and special bitwise assignment operators: +=, -=, *=,
// /=, %=, &=, |=, ^=, <<=, >>=, <<<=, and >>>=". Each of them stores into its
// left-hand side, which is the state change §37.3.5 calls a side effect.
static bool IsAssignmentOperator(TokenKind op) {
  switch (op) {
    case TokenKind::kEq:
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

// §37.3.5's first two bullets, which are decided by the expression's own form:
// an assignment operator (§11.4.1) or an increment or decrement operator
// (§11.4.2), the latter written either side of its operand.
static bool ExprIsSideEffectingForm(const Expr* expr) {
  if (expr->kind == ExprKind::kUnary || expr->kind == ExprKind::kPostfixUnary) {
    return expr->op == TokenKind::kPlusPlus ||
           expr->op == TokenKind::kMinusMinus;
  }
  return expr->kind == ExprKind::kBinary && IsAssignmentOperator(expr->op);
}

bool VpiSourceExprHasSideEffects(const Expr* expr) {
  if (expr == nullptr) return false;
  if (ExprIsSideEffectingForm(expr)) return true;

  // §37.3.5's fourth bullet: an expression with side effects as an operand, an
  // argument or an index expression of another gives that one side effects
  // too. Every place a
  // subexpression can be written is one of those three, so the whole expression
  // is walked rather than a chosen few of its edges.
  const Expr* const kEdges[] = {
      expr->lhs,        expr->rhs,         expr->condition, expr->true_expr,
      expr->false_expr, expr->base,        expr->index,     expr->index_end,
      expr->with_expr,  expr->repeat_count};
  for (const Expr* edge : kEdges) {
    if (VpiSourceExprHasSideEffects(edge)) return true;
  }
  for (const Expr* arg : expr->args) {
    if (VpiSourceExprHasSideEffects(arg)) return true;
  }
  for (const Expr* element : expr->elements) {
    if (VpiSourceExprHasSideEffects(element)) return true;
  }
  for (const Expr* key : expr->pattern_keys) {
    if (VpiSourceExprHasSideEffects(key)) return true;
  }
  return false;
}

}  // namespace delta
