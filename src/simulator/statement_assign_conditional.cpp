// §11.4.11 for a conditional whose operands are queues, dynamic arrays or
// associative arrays assigned whole, which a value of one vector cannot carry.

#include <cstddef>
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
  if (queue != nullptr) {
    const QueueObject* a = ctx.FindQueue(rhs->true_expr->text);
    const QueueObject* b = ctx.FindQueue(rhs->false_expr->text);
    if (a == nullptr || b == nullptr) return false;
    AssignMergedQueues(queue, *a, *b, arena);
  } else {
    const AssocArrayObject* a = ctx.FindAssocArray(rhs->true_expr->text);
    const AssocArrayObject* b = ctx.FindAssocArray(rhs->false_expr->text);
    if (a == nullptr || b == nullptr) return false;
    const bool kSame = SameAssocContents(*a, *b);
    assoc->int_data = kSame ? a->int_data : decltype(assoc->int_data){};
    assoc->str_data = kSame ? a->str_data : decltype(assoc->str_data){};
  }
  NotifyOwningVar(ctx, kTarget);
  return true;
}

}  // namespace delta
