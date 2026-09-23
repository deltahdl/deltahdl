#include "simulator/eval_array_element_queue.h"

#include <cstdint>
#include <map>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// An empty queue whose elements are `width` bits, four-state where
// `is_4state` says so and class handles where `handles` does.
QueueObject* NewElementQueue(uint32_t width, bool is_4state, bool handles,
                             Arena& arena) {
  auto* q = arena.Create<QueueObject>();
  q->elem_width = width;
  q->is_4state = is_4state;
  q->holds_class_handles = handles;
  return q;
}

// The entries of an associative array under one kind of key, `data`, and the
// queue each element that is a queue holds under the same key, `queues`.
template <typename Key>
struct KeyedEntries {
  std::map<Key, Logic4Vec>& data;
  std::map<Key, QueueObject*>& queues;
};

// The queue under `key` of the associative array `aa`, whose entries under
// that kind of key are `entries`. A key the entries lack is allocated where
// `allocate` says so, the queue a deleted entry left under it dropped so the
// new element starts empty (§7.8.7); read alone, it answers a fresh empty
// queue and allocates nothing.
template <typename Key>
QueueObject* AssocElementQueue(AssocArrayObject* aa, KeyedEntries<Key> entries,
                               const Key& key, bool allocate, Arena& arena) {
  if (entries.data.count(key) == 0) {
    if (!allocate) {
      return NewElementQueue(aa->elem_width, aa->is_4state,
                             aa->element_queue_handles, arena);
    }
    entries.data.emplace(key, AssocAllocValue(aa, arena));
    entries.queues.erase(key);
  }
  QueueObject*& q = entries.queues[key];
  if (q == nullptr) {
    q = NewElementQueue(aa->elem_width, aa->is_4state,
                        aa->element_queue_handles, arena);
  }
  return q;
}

// §7.8: the element `sel` selects of the associative array `aa`, keyed as the
// array keys its entries (AssocStringKey, AssocIntKey).
QueueObject* OfAssocElement(AssocArrayObject* aa, const Expr* sel,
                            SimContext& ctx, Arena& arena, bool allocate) {
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (aa->is_string_key) {
    return AssocElementQueue(
        aa, KeyedEntries<std::string>{aa->str_data, aa->str_element_queues},
        AssocStringKey(idx), allocate, arena);
  }
  if (HasUnknownBits(idx)) return nullptr;
  int64_t key =
      AssocIntKey(idx, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  return AssocElementQueue(
      aa, KeyedEntries<int64_t>{aa->int_data, aa->int_element_queues}, key,
      allocate, arena);
}

// §7.10.1: the element `sel` selects of the queue or dynamic array `outer`,
// `$` in the index standing for the last position. The element's queue is
// kept under the element's identity where `outer` keeps identities, so a
// push_front or a pop on `outer` leaves each element with its own queue, and
// under the position otherwise.
QueueObject* OfQueueElement(QueueObject* outer, const Expr* sel,
                            SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  auto* last = ctx.CreateLocalVariable("$", 32);
  last->value = MakeLogic4VecVal(
      arena, 32, outer->elements.empty() ? 0 : outer->elements.size() - 1);
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  ctx.PopScope();
  if (HasUnknownBits(idx)) return nullptr;
  uint64_t pos = idx.ToUint64();
  if (pos >= outer->elements.size()) return nullptr;
  uint64_t key = outer->element_ids.size() == outer->elements.size()
                     ? outer->element_ids[pos]
                     : pos;
  QueueObject*& q = outer->element_queues[key];
  if (q == nullptr) {
    q = NewElementQueue(outer->elem_width, outer->is_4state,
                        outer->holds_class_handles, arena);
  }
  return q;
}

// Appends to `q` what `item` contributes as an item of an unpacked array
// concatenation (§10.10): a queue's elements where it designates one, else its
// one value, sized to the element type.
void AppendItem(QueueObject* q, const Expr* item, SimContext& ctx,
                Arena& arena) {
  if (const QueueObject* src = FindQueueOfBase(item, ctx, arena)) {
    q->elements.insert(q->elements.end(), src->elements.begin(),
                       src->elements.end());
    return;
  }
  q->elements.push_back(
      SizedForQueueElement(*q, EvalExpr(item, ctx, arena), arena));
}

// §7.4: the element `sel` selects of a fixed-size array whose elements are
// queues, which is the queue created under the element's own name
// (CreateFixedElementQueues in lowerer_var_aggregate.cpp); null for an index
// holding an x or z bit or one outside the array.
QueueObject* OfFixedElement(const Expr* sel, SimContext& ctx, Arena& arena) {
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (HasUnknownBits(idx)) return nullptr;
  return ctx.FindQueue(std::string(sel->base->text) + "[" +
                       std::to_string(idx.ToUint64()) + "]");
}

}  // namespace

QueueObject* ElementQueueFromItem(const QueueObject* outer, const Expr* item,
                                  SimContext& ctx, Arena& arena) {
  QueueObject* q = NewElementQueue(outer->elem_width, outer->is_4state,
                                   outer->holds_class_handles, arena);
  bool listed = item->kind == ExprKind::kConcatenation ||
                (item->kind == ExprKind::kAssignmentPattern &&
                 item->pattern_keys.empty());
  if (listed) {
    for (const Expr* element : item->elements)
      AppendItem(q, element, ctx, arena);
  } else {
    AppendItem(q, item, ctx, arena);
  }
  q->AllocateIdsForAppended();
  return q;
}

QueueObject* ElementQueueOfSelect(const Expr* sel, SimContext& ctx,
                                  Arena& arena, bool allocate) {
  if (sel == nullptr || sel->kind != ExprKind::kSelect ||
      sel->base == nullptr || sel->index == nullptr ||
      sel->index_end != nullptr) {
    return nullptr;
  }
  if (AssocArrayObject* aa = FindAssocArrayOfBase(sel->base, ctx, arena);
      aa != nullptr && aa->elements_are_queues) {
    return OfAssocElement(aa, sel, ctx, arena, allocate);
  }
  if (sel->base->kind == ExprKind::kIdentifier) {
    const ArrayInfo* info = ctx.FindArrayInfo(sel->base->text);
    if (info != nullptr && info->elements_are_queues)
      return OfFixedElement(sel, ctx, arena);
  }
  QueueObject* outer = FindQueueOfBase(sel->base, ctx, arena);
  if (outer == nullptr || !outer->elements_are_queues) return nullptr;
  return OfQueueElement(outer, sel, ctx, arena);
}

}  // namespace delta
