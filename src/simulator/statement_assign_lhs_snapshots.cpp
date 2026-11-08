#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

struct IndexWalk {
  SimContext& ctx;
  Arena& arena;
  LhsIndexSnapshots& out;
  bool unsettled_only;
};

}  // namespace

static bool MentionsDollar(const Expr* expr) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier && expr->text == "$") return true;
  const Expr* const kEdges[] = {
      expr->lhs,        expr->rhs,  expr->condition, expr->true_expr,
      expr->false_expr, expr->base, expr->index,     expr->index_end};
  for (const Expr* edge : kEdges) {
    if (MentionsDollar(edge)) return true;
  }
  for (const Expr* arg : expr->args) {
    if (MentionsDollar(arg)) return true;
  }
  for (const Expr* element : expr->elements) {
    if (MentionsDollar(element)) return true;
  }
  return false;
}

static bool IndexIsSettled(const Expr* node, SimContext& ctx) {
  if (ctx.FindDeferredArgSnapshot(node) != nullptr) return true;
  if (MentionsDollar(node)) return true;
  if (node->kind == ExprKind::kIntegerLiteral) return true;
  return node->kind == ExprKind::kIdentifier &&
         NameDenotesVariable(IdentifierLookupKey(node), ctx);
}

static void CollectIndexSnapshot(const Expr* node, IndexWalk& walk) {
  if (!node) return;
  if (walk.unsettled_only && IndexIsSettled(node, walk.ctx)) return;
  walk.out.emplace_back();
  walk.out.back().first = node;
  walk.out.back().second.Capture(EvalExpr(node, walk.ctx, walk.arena));
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, IndexWalk& walk);

static void CollectSelectIndices(const Expr* sel, IndexWalk& walk) {
  CollectIndexSnapshot(sel->index, walk);
  CollectIndexSnapshot(sel->index_end, walk);
  CollectLhsIndexSnapshotsInto(sel->base, walk);
}

static void CollectElementIndices(const Expr* expr, IndexWalk& walk) {
  for (const auto* elem : expr->elements) {
    if (!elem) continue;
    if (elem->stream_range) {
      CollectIndexSnapshot(elem->stream_range->index, walk);
      CollectIndexSnapshot(elem->stream_range->index_end, walk);
    }
    CollectLhsIndexSnapshotsInto(elem, walk);
  }
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, IndexWalk& walk) {
  if (!lhs) return;
  const Expr* target = UnwrapTypedPattern(lhs);
  if (!target) return;
  switch (target->kind) {
    case ExprKind::kSelect:
      CollectSelectIndices(target, walk);
      break;
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kStreamingConcat:
      CollectElementIndices(target, walk);
      break;
    case ExprKind::kMemberAccess:
      CollectLhsIndexSnapshotsInto(target->lhs, walk);
      break;
    default:
      break;
  }
}

LhsIndexSnapshots CollectLhsIndexSnapshots(const Expr* lhs, SimContext& ctx,
                                           Arena& arena) {
  LhsIndexSnapshots out;
  IndexWalk walk{ctx, arena, out, false};
  CollectLhsIndexSnapshotsInto(lhs, walk);
  return out;
}

void InstallLhsIndexSnapshots(const LhsIndexSnapshots& snaps, SimContext& ctx) {
  for (const auto& snap : snaps) {
    ctx.SetDeferredArgSnapshot(snap.first, snap.second.Get());
  }
}

void ClearLhsIndexSnapshots(const LhsIndexSnapshots& snaps, SimContext& ctx) {
  for (const auto& snap : snaps) ctx.ClearDeferredArgSnapshot(snap.first);
}

LhsIndexPin::LhsIndexPin(const Expr* lhs, SimContext& ctx, Arena& arena)
    : ctx_(&ctx) {
  IndexWalk walk{ctx, arena, snaps_, true};
  CollectLhsIndexSnapshotsInto(lhs, walk);
  InstallLhsIndexSnapshots(snaps_, ctx);
}

LhsIndexPin::~LhsIndexPin() { ClearLhsIndexSnapshots(snaps_, *ctx_); }

}  // namespace delta
