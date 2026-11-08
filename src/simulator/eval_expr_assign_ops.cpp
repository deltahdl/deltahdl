#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/operator_classes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static Logic4Vec ApplyRealUnaryOp(const Logic4Vec& old_val, double delta,
                                  Arena& arena) {
  return MakeRealVec(arena, RealVecToDouble(old_val) + delta, old_val.width);
}

struct IncDecResult {
  Logic4Vec old_val;
  Logic4Vec new_val;
};

static void StoreOperatorResult(Variable* var, Logic4Vec& result) {
  if (!var->is_4state) CoerceTo2State(result);
  if (!var->is_forced) {
    var->value = result;
    var->NotifyWatchers();
  }
}

static Variable* WholeVariableOfMember(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind != ExprKind::kMemberAccess) return nullptr;
  return ResolveLhsVariable(lhs, ctx);
}

static void WriteIncDecTarget(const Expr* lhs, Logic4Vec& new_val,
                              SimContext& ctx, Arena& arena) {
  if (lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(lhs, new_val, ctx, arena);
    return;
  }
  if (auto* whole = WholeVariableOfMember(lhs, ctx)) {
    StoreOperatorResult(whole, new_val);
    return;
  }
  if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, new_val, ctx);
    return;
  }
  if (lhs->kind != ExprKind::kIdentifier) return;
  auto* var = ctx.FindVariable(lhs->text);
  if (var == nullptr) {
    TryFuncClassPropertyWrite(lhs, new_val, ctx, arena);
    return;
  }
  StoreOperatorResult(var, new_val);
}

static IncDecResult EvalIncDec(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  SnapshotSelectIndices(expr->lhs, ctx, arena);
  AllocateAssocEntryForModify(expr->lhs, ctx, arena);
  auto old_val = EvalExpr(expr->lhs, ctx, arena);
  Logic4Vec new_val;
  if (old_val.is_real) {
    new_val = ApplyRealUnaryOp(
        old_val, (expr->op == TokenKind::kPlusPlus) ? 1.0 : -1.0, arena);
  } else {
    auto one = MakeLogic4VecVal(arena, old_val.width, 1);
    one.is_signed = old_val.is_signed;
    new_val =
        EvalBinaryOp((expr->op == TokenKind::kPlusPlus) ? TokenKind::kPlus
                                                        : TokenKind::kMinus,
                     old_val, one, arena);
  }
  WriteIncDecTarget(expr->lhs, new_val, ctx, arena);
  ClearSelectIndices(expr->lhs, ctx);
  return {old_val, new_val};
}

Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).new_val;
}

Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena) {
  return EvalIncDec(expr, ctx, arena).old_val;
}

TokenKind CompoundAssignBaseOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
      return TokenKind::kPlus;
    case TokenKind::kMinusEq:
      return TokenKind::kMinus;
    case TokenKind::kStarEq:
      return TokenKind::kStar;
    case TokenKind::kSlashEq:
      return TokenKind::kSlash;
    case TokenKind::kPercentEq:
      return TokenKind::kPercent;
    case TokenKind::kAmpEq:
      return TokenKind::kAmp;
    case TokenKind::kPipeEq:
      return TokenKind::kPipe;
    case TokenKind::kCaretEq:
      return TokenKind::kCaret;
    case TokenKind::kLtLtEq:
      return TokenKind::kLtLt;
    case TokenKind::kGtGtEq:
      return TokenKind::kGtGt;
    case TokenKind::kLtLtLtEq:
      return TokenKind::kLtLtLt;
    case TokenKind::kGtGtGtEq:
      return TokenKind::kGtGtGt;
    default:
      return TokenKind::kEof;
  }
}

bool IsCompoundAssignOp(TokenKind op) {
  return CompoundAssignBaseOp(op) != TokenKind::kEof;
}

Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena) {
  SnapshotSelectIndices(expr->lhs, ctx, arena);
  AllocateAssocEntryForModify(expr->lhs, ctx, arena);
  uint32_t target_width = LhsContextWidth(expr->lhs, ctx, arena);
  uint32_t yield_width = target_width;
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena,
                          IsMaxWidthBinaryOp(base_op) ? target_width : 0);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena, target_width);
  if (auto* whole = WholeVariableOfMember(expr->lhs, ctx)) {
    result = ConvertRealOnAssign(result, expr->lhs, *whole, ctx, arena);
    result = ResizeToWidth(result, whole->value.width, arena);
    yield_width = whole->value.width;
    StoreOperatorResult(whole, result);
  } else if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) {
      result = ConvertRealOnAssign(result, expr->lhs, *var, ctx, arena);
      StoreOperatorResult(var, result);
    } else {
      TryFuncClassPropertyWrite(expr->lhs, result, ctx, arena);
    }
  } else if (expr->lhs->kind == ExprKind::kSelect) {
    TrySelectBlockingAssign(expr->lhs, result, ctx, arena);
  } else if (expr->lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(expr->lhs, result, ctx, &yield_width);
  }
  ClearSelectIndices(expr->lhs, ctx);
  if (yield_width != 0 && yield_width != result.width)
    return ResizeToWidth(result, yield_width, arena);
  return result;
}

}  // namespace delta
