// §11.4.11 for a conditional whose operands are queues, dynamic arrays or
// associative arrays assigned whole, which a value of one vector cannot carry.

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

// Whether `a` and `b` are logically equal (§11.4.5): every bit known and the
// same.
bool LogicallyEqual(const Logic4Vec& a, const Logic4Vec& b) {
  return !HasUnknownBits(a) && !HasUnknownBits(b) && a.SameValueAs(b);
}

// §11.4.11: under an ambiguous predicate, arrays holding as many elements are
// combined element by element -- an element both hold alike kept, any other
// given its type's Table 7-1 default -- and arrays holding different counts
// give the result type's default, an empty array.
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

// Whether two associative arrays hold the same keys with logically equal
// values.
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

// The queues or dynamic arrays the conditional `rhs` names, merged into
// `queue`; false where either names none.
bool MergeQueueOperands(QueueObject* queue, const Expr* rhs, SimContext& ctx,
                        Arena& arena) {
  const QueueObject* a = ctx.FindQueue(rhs->true_expr->text);
  const QueueObject* b = ctx.FindQueue(rhs->false_expr->text);
  if (a == nullptr || b == nullptr) return false;
  AssignMergedQueues(queue, *a, *b, arena);
  return true;
}

// The associative arrays the conditional `rhs` names: their shared contents
// where they are equal, and nothing where they are not, stored in `assoc`;
// false where either names none.
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

// §11.4.11 with Table 7-1: the element an unknown predicate yields from the two
// arms' elements `t` and `e` -- the value both hold where they match, and the
// element type's default, x for a four-state type and 0 for a two-state one,
// where they do not.
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

// Whether the known predicate `cond` holds: any bit of it set.
bool KnownPredicateHolds(const Logic4Vec& cond) {
  for (uint32_t w = 0; w < cond.nwords; ++w) {
    if (cond.words[w].aval != 0) return true;
  }
  return false;
}

// Writes each element of the array `dst_name` describes by `dst` the element
// MergedConditionalElement makes of the elements of the conditional `cond`'s
// two arms at the same position, left to right.
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

// §11.4.11 with §7.5, §7.8 and §7.10: a known predicate assigns the chosen
// array whole, as an assignment of it alone would; an ambiguous one assigns
// queues and dynamic arrays merged element by element, and an associative
// array -- left out of that merge -- the shared contents where the two are
// equal and the empty array, its Table 7-1 default, where they are not.
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

// §11.4.11: `r = c ? a : b` over fixed-size unpacked arrays. A known predicate
// copies the array it selects whole; an unknown one merges the two arms
// element by element (WriteMergedConditionalArray). Evaluated as a value, the
// conditional read each arm's name as one element, and nothing reached `r`.
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
