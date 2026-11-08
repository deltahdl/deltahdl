#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiObjectCarriesSourceDelay(int type) {
  switch (type) {
    case vpiPrimitive:
    case vpiGate:
    case vpiSwitch:
    case vpiUdp:
    case vpiModPath:
    case vpiTchk:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiGateArray:
    case vpiSwitchArray:
    case vpiUdpArray:
      return true;
    default:
      return VpiIsNetsType(type);
  }
}

VpiHandle VpiSourceDelayExpr(VpiHandle obj) {
  if (!obj) return nullptr;
  if (!VpiObjectCarriesSourceDelay(obj->type)) return nullptr;
  return obj->delay_expr;
}

bool VpiSourceDelayExprIsListOp(VpiHandle expr) {
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

bool VpiExpressionHasSideEffects(const VpiObject* obj) {
  return obj && obj->has_side_effects;
}

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

  const Expr* const kEdges[] = {
      expr->lhs,        expr->rhs,          expr->condition,   expr->true_expr,
      expr->false_expr, expr->base,         expr->index,       expr->index_end,
      expr->with_expr,  expr->stream_range, expr->repeat_count};
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
