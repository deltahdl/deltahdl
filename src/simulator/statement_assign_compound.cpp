
#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assoc_element.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §11.4.1: a compound assignment evaluates any left-hand index expression only
// once. The resolve/read/write helpers below each re-derive the target from
// lhs->index (and index_end) by calling EvalExpr on those nodes, which would
// invoke a side-effecting index (e.g. `data[f()] += 1`) several times. Evaluate
// each index expression a single time up front and stash the result as a
// per-expression snapshot; EvalExpr returns a stored snapshot ahead of any real
// evaluation, so every later read of the same index node reuses this value.
void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx, Arena& arena) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  SnapshotSelectIndices(lhs->base, ctx, arena);
  if (lhs->index != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index, EvalExpr(lhs->index, ctx, arena));
  if (lhs->index_end != nullptr)
    ctx.SetDeferredArgSnapshot(lhs->index_end,
                               EvalExpr(lhs->index_end, ctx, arena));
}

// Undoes SnapshotSelectIndices once the compound assignment has finished so the
// snapshots do not leak into later statements that reuse the same index nodes.
void ClearSelectIndices(const Expr* lhs, SimContext& ctx) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return;
  ClearSelectIndices(lhs->base, ctx);
  if (lhs->index != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index);
  if (lhs->index_end != nullptr) ctx.ClearDeferredArgSnapshot(lhs->index_end);
}

// §26.3 with §11.4.1: `p::shared += n` names the package's whole variable
// through the scope resolution operator, held under "p.shared", which the
// plain assignment resolves ahead of a structure member (ResolveLhsVariable
// before WriteStructField in ExecBlockingAssign) and the expression form in
// eval_expr_assign_ops.cpp does the same; WriteStructField alone took `p` for
// a variable, found none, and wrote nothing. A member of a structure variable
// resolves to no whole variable and takes the field write as before.
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

void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto base_op = CompoundAssignBaseOp(stmt->rhs->op);
  auto actual_rhs = EvalExpr(stmt->rhs->rhs, ctx, arena);

  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ResolveLhsVariable(stmt->lhs, ctx);
    if (var) {
      auto result = EvalBinaryOp(base_op, var->value, actual_rhs, arena);
      // §6.12.1's conversion, which WriteVar does not apply: `int i; i += 1.5;`
      // computes a real and stores an integer.
      result = ConvertRealOnAssign(result, stmt->lhs, *var, ctx, arena);
      WriteVar(var, result, arena);
    }
  } else if (stmt->lhs->kind == ExprKind::kSelect) {
    SnapshotSelectIndices(stmt->lhs, ctx, arena);
    if (auto* elem = TryResolveArrayElement(stmt->lhs, ctx)) {
      auto result = EvalBinaryOp(base_op, elem->value, actual_rhs, arena);
      WriteVar(elem, result, arena);
    } else {
      // §7.8.7: a compound assignment reads and writes in one statement, so a
      // nonexistent associative array element is allocated with its initial
      // value before the read below rather than by the write after it.
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
