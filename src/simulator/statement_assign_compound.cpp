#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/operator_classes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assoc_element.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  SnapshotSelectIndices(lhs->base, ctx, arena);
  if (lhs->index != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index, EvalExpr(lhs->index, ctx, arena));
  if (lhs->index_end != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index_end,
                               EvalExpr(lhs->index_end, ctx, arena));
}

void ClearSelectIndices(const Expr* lhs, SimContext& ctx) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  ClearSelectIndices(lhs->base, ctx);
  if (lhs->index != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index);
  if (lhs->index_end != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index_end);
}

static void CompoundAssignToMember(const Stmt* stmt, TokenKind base_op,
                                   const Logic4Vec& actual_rhs, SimContext& ctx,
                                   Arena& arena) {
  if (auto* whole = ResolveLhsVariable(stmt->lhs, ctx)) {
    auto result = EvalBinaryOp(base_op, whole->value, actual_rhs, arena);
    result = ConvertRealOnAssign(result, stmt->lhs, *whole, ctx, arena);
    WriteVar(whole, result, arena);
    return;
  }
  auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
  auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
  WriteStructField(stmt->lhs, result, ctx);
}

uint32_t CompoundOperandWidth(TokenKind base_op, const Expr* lhs,
                              SimContext& ctx, Arena& arena) {
  return IsMaxWidthBinaryOp(base_op) ? LhsContextWidth(lhs, ctx, arena) : 0;
}

void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto base_op = CompoundAssignBaseOp(stmt->rhs->op);
  SnapshotSelectIndices(stmt->lhs, ctx, arena);
  auto actual_rhs =
      EvalExpr(stmt->rhs->rhs, ctx, arena,
               CompoundOperandWidth(base_op, stmt->lhs, ctx, arena));

  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ResolveLhsVariable(stmt->lhs, ctx);
    if (var) {
      auto result = EvalBinaryOp(base_op, var->value, actual_rhs, arena);
      result = ConvertRealOnAssign(result, stmt->lhs, *var, ctx, arena);
      WriteVar(var, result, arena);
    }
  } else if (stmt->lhs->kind == ExprKind::kSelect) {
    if (auto* elem = TryResolveArrayElement(stmt->lhs, ctx)) {
      auto result = EvalBinaryOp(base_op, elem->value, actual_rhs, arena);
      WriteVar(elem, result, arena);
    } else {
      AllocateAssocEntryForModify(stmt->lhs, ctx, arena);
      auto lhs_val = EvalExpr(stmt->lhs, ctx, arena);
      auto result = EvalBinaryOp(base_op, lhs_val, actual_rhs, arena);
      TrySelectBlockingAssign(stmt->lhs, result, ctx, arena);
    }
    ClearSelectIndices(stmt->lhs, ctx);
  } else if (stmt->lhs->kind == ExprKind::kMemberAccess) {
    CompoundAssignToMember(stmt, base_op, actual_rhs, ctx, arena);
  } else {
    auto result = EvalExpr(stmt->rhs, ctx, arena);
    AssignToScalarLhs(stmt, result, ctx, arena);
  }
}

}  // namespace delta
