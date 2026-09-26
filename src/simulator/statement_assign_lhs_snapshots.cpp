#include <string>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// The index expressions a left-hand side carries, each paired with the value it
// has when the pair is made, for a caller to install as the deferred-argument
// snapshots EvalExpr answers from before it evaluates anything: a nonblocking
// assignment's brace targets, whose unpackers run in the update region and read
// the values the statement saw (§10.4.2), and a blocking store, whose writers
// each re-derive the target from the same nodes and must see one evaluation of
// them (§10.4.1).

namespace {

// One walk over a left-hand side's index nodes: the context they are evaluated
// in, where the pairs go, and whether a node whose evaluation could change
// nothing is passed over.
struct IndexWalk {
  SimContext& ctx;
  Arena& arena;
  LhsIndexSnapshots& out;
  bool unsettled_only;
};

}  // namespace

// Whether pinning `node` for a blocking store would change nothing: a node
// some caller has pinned already, whose value EvalExpr returns without
// evaluating it, a literal, or a bare name of a variable, whose evaluation
// reads one value and stores nothing. A bare name that is no variable may be a
// method's call (§13.5.5) or a let's expansion (§11.12), each evaluating more
// than the name shows, so it is pinned like any other expression.
static bool IndexIsSettled(const Expr* node, SimContext& ctx) {
  if (ctx.FindDeferredArgSnapshot(node) != nullptr) return true;
  if (node->kind == ExprKind::kIntegerLiteral) return true;
  return node->kind == ExprKind::kIdentifier &&
         NameDenotesVariable(IdentifierLookupKey(node), ctx);
}

// Pair `node` with its value now, when there is a node to pair. A constant
// index is paired like any other where the walk takes every node: it
// re-evaluates to the same value, so the snapshot costs one entry and asks the
// walk no question about the expression.
static void CollectIndexSnapshot(const Expr* node, IndexWalk& walk) {
  if (!node) return;
  if (walk.unsettled_only && IndexIsSettled(node, walk.ctx)) return;
  walk.out.emplace_back();
  walk.out.back().first = node;
  walk.out.back().second.Capture(EvalExpr(node, walk.ctx, walk.arena));
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, IndexWalk& walk);

// The indices of a select: its own, and then those of its base, since §7.4.5's
// indexed name can name a select of a select.
static void CollectSelectIndices(const Expr* sel, IndexWalk& walk) {
  CollectIndexSnapshot(sel->index, walk);
  CollectIndexSnapshot(sel->index_end, walk);
  CollectLhsIndexSnapshotsInto(sel->base, walk);
}

// The indices under each element of a concatenation, an assignment pattern or a
// streaming concatenation. §11.4.14.3's `with` range is an index expression of
// the element it qualifies -- ResolveWithRange evaluates it -- so it is taken
// here alongside the element's own.
static void CollectElementIndices(const Expr* expr, IndexWalk& walk) {
  for (const auto* elem : expr->elements) {
    if (!elem) continue;
    if (elem->with_expr) {
      CollectIndexSnapshot(elem->with_expr->index, walk);
      CollectIndexSnapshot(elem->with_expr->index_end, walk);
    }
    CollectLhsIndexSnapshotsInto(elem, walk);
  }
}

static void CollectLhsIndexSnapshotsInto(const Expr* lhs, IndexWalk& walk) {
  if (!lhs) return;
  // §10.9's type prefix is a cast around the pattern, and a nested
  // concatenation is one of the forms UnpackConcatLhs walks, so the walk looks
  // through the prefix at every level rather than only at the top.
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

// §10.4.1 (printed page 252) evaluates the index expressions a variable_lvalue
// carries at one time, and §10.4.2 (printed page 253) the nonblocking form's at
// the time it evaluates the right-hand side. The writers a store asks in turn
// each re-derive the target from the same index nodes -- the fixed-size array
// element's name, then the queue's, then the associative array's, then the
// window of a packed select -- and the first to decline had already evaluated
// them, so `d[j++] = 7` on a dynamic array incremented j twice and wrote the
// element the second value named. Pinning each index a store could evaluate to
// a different end for the length of the store makes every writer read the one
// value. A node already pinned is left to whoever pinned it, so a store reached
// from inside another's pin clears only what it added.
LhsIndexPin::LhsIndexPin(const Expr* lhs, SimContext& ctx, Arena& arena)
    : ctx_(&ctx) {
  IndexWalk walk{ctx, arena, snaps_, true};
  CollectLhsIndexSnapshotsInto(lhs, walk);
  InstallLhsIndexSnapshots(snaps_, ctx);
}

LhsIndexPin::~LhsIndexPin() { ClearLhsIndexSnapshots(snaps_, *ctx_); }

}  // namespace delta
