#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

bool LogicallyEqual(const Logic4Vec& a, const Logic4Vec& b) {
  return !HasUnknownBits(a) && !HasUnknownBits(b) && a.SameValueAs(b);
}

void AssignMergedQueues(QueueObject* dst, const QueueObject& a,
                        const QueueObject& b, Arena& arena) {
  std::vector<Logic4Vec> merged;
  if (a.elements.size() == b.elements.size()) {
    for (size_t i = 0; i < a.elements.size(); ++i) {
      merged.push_back(LogicallyEqual(a.elements[i], b.elements[i])
                           ? a.elements[i]
                           : NonexistentQueueElement(dst, arena));
    }
  }
  dst->elements = std::move(merged);
  dst->AssignFreshIds();
  ++dst->generation;
}

bool SameAssocContents(const AssocArrayObject& a, const AssocArrayObject& b) {
  auto same = [](const auto& x, const auto& y) {
    if (x.size() != y.size()) return false;
    for (auto i = x.begin(), j = y.begin(); i != x.end(); ++i, ++j) {
      const bool kSameKey = !x.key_comp()(i->first, j->first) &&
                            !x.key_comp()(j->first, i->first);
      if (!kSameKey || !LogicallyEqual(i->second, j->second)) return false;
    }
    return true;
  };
  return same(a.int_data, b.int_data) && same(a.str_data, b.str_data);
}

bool MergeQueueOperands(QueueObject* queue, const Expr* rhs, SimContext& ctx,
                        Arena& arena) {
  const QueueObject* a = ctx.FindQueue(rhs->true_expr->text);
  const QueueObject* b = ctx.FindQueue(rhs->false_expr->text);
  if (a == nullptr || b == nullptr) return false;
  AssignMergedQueues(queue, *a, *b, arena);
  return true;
}

bool MergeAssocOperands(AssocArrayObject* assoc, const Expr* rhs,
                        SimContext& ctx) {
  const AssocArrayObject* a = ctx.FindAssocArray(rhs->true_expr->text);
  const AssocArrayObject* b = ctx.FindAssocArray(rhs->false_expr->text);
  if (a == nullptr || b == nullptr) return false;
  const bool kSame = SameAssocContents(*a, *b);
  assoc->int_data = kSame ? a->int_data : decltype(assoc->int_data){};
  assoc->str_data = kSame ? a->str_data : decltype(assoc->str_data){};
  return true;
}

Logic4Vec MergedConditionalElement(const Logic4Vec& t, const Logic4Vec& e,
                                   const ArrayInfo& dst, Arena& arena) {
  Logic4Vec a = ResizeToWidth(t, dst.elem_width, arena);
  Logic4Vec b = ResizeToWidth(e, dst.elem_width, arena);
  bool same = true;
  for (uint32_t w = 0; w < a.nwords && same; ++w)
    same = a.words[w].aval == b.words[w].aval &&
           a.words[w].bval == b.words[w].bval;
  if (same) return OwnRhsWords(a, arena);
  return dst.is_4state ? MakeAllX(arena, dst.elem_width)
                       : MakeLogic4VecVal(arena, dst.elem_width, 0);
}

bool KnownPredicateHolds(const Logic4Vec& cond) {
  for (uint32_t w = 0; w < cond.nwords; ++w) {
    if (cond.words[w].aval != 0) return true;
  }
  return false;
}

void WriteMergedConditionalArray(std::string_view dst_name,
                                 const ArrayInfo& dst, const Expr* cond,
                                 SimContext& ctx, Arena& arena) {
  const Expr* t = cond->true_expr;
  const Expr* e = cond->false_expr;
  std::vector<Logic4Vec> tv;
  std::vector<Logic4Vec> ev;
  CollectFixedArrayElements(t->text, *ctx.FindArrayInfo(t->text), ctx, tv);
  CollectFixedArrayElements(e->text, *ctx.FindArrayInfo(e->text), ctx, ev);
  size_t count =
      std::min({static_cast<size_t>(dst.size), tv.size(), ev.size()});
  for (size_t i = 0; i < count; ++i) {
    auto offset = static_cast<uint32_t>(i);
    uint32_t idx =
        dst.is_descending ? dst.lo + dst.size - 1 - offset : dst.lo + offset;
    Variable* var = ctx.FindVariable(std::string(dst_name) + "[" +
                                     std::to_string(idx) + "]");
    if (var == nullptr) continue;
    var->value = MergedConditionalElement(tv[i], ev[i], dst, arena);
    var->NotifyWatchers();
  }
}

}  // namespace

bool TryConditionalCollectionAssign(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (rhs == nullptr || rhs->kind != ExprKind::kTernary ||
      stmt->lhs->kind != ExprKind::kIdentifier ||
      rhs->true_expr->kind != ExprKind::kIdentifier ||
      rhs->false_expr->kind != ExprKind::kIdentifier)
    return false;
  const std::string_view kTarget = stmt->lhs->text;
  QueueObject* queue = ctx.FindQueue(kTarget);
  AssocArrayObject* assoc = ctx.FindAssocArray(kTarget);
  if (queue == nullptr && assoc == nullptr) return false;
  const Truth kPredicate = TruthOf(EvalExpr(rhs->condition, ctx, arena));
  if (kPredicate != Truth::kAmbiguous) {
    auto* chosen = arena.Create<Stmt>(*stmt);
    chosen->rhs = kPredicate == Truth::kTrue ? rhs->true_expr : rhs->false_expr;
    ExecBlockingAssignImpl(chosen, ctx, arena);
    return true;
  }
  const bool kMerged = queue != nullptr
                           ? MergeQueueOperands(queue, rhs, ctx, arena)
                           : MergeAssocOperands(assoc, rhs, ctx);
  if (kMerged) NotifyOwningVar(ctx, kTarget);
  return kMerged;
}

bool TryConditionalArrayAssign(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  const Expr* rhs = stmt->rhs;
  if (rhs == nullptr || rhs->kind != ExprKind::kTernary ||
      stmt->lhs->kind != ExprKind::kIdentifier)
    return false;
  const ArrayInfo* dst = ctx.FindArrayInfo(stmt->lhs->text);
  const Expr* t = rhs->true_expr;
  const Expr* e = rhs->false_expr;
  if (dst == nullptr || dst->is_dynamic || dst->is_queue ||
      !dst->dim_sizes.empty() || t->kind != ExprKind::kIdentifier ||
      e->kind != ExprKind::kIdentifier || !ctx.FindArrayInfo(t->text) ||
      !ctx.FindArrayInfo(e->text))
    return false;
  Logic4Vec cond = EvalExpr(rhs->condition, ctx, arena);
  if (!cond.IsKnown()) {
    WriteMergedConditionalArray(stmt->lhs->text, *dst, rhs, ctx, arena);
    return true;
  }
  const Expr* src = KnownPredicateHolds(cond) ? t : e;
  CopyArrayElements(stmt->lhs->text, *dst, src->text,
                    *ctx.FindArrayInfo(src->text), ctx);
  return true;
}

}  // namespace delta
