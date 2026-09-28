#include "simulator/eval_array_element_queue.h"

#include <cstdint>
#include <map>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// What each element's queue of an array whose elements are queues is made
// of: elements of `width` bits, four-state where `is_4state` says so, class
// handles where `handles` does, `levels` further levels of queues below it
// (QueueObject::nested_queue_levels), and, where the element is a fixed-size
// array, `fixed_size` elements (QueueObject::element_array_size).
struct ElementQueueShape {
  uint32_t width;
  bool is_4state;
  bool handles;
  uint32_t levels;
  uint32_t fixed_size = 0;
};

ElementQueueShape ShapeOf(const QueueObject& outer) {
  return {outer.elem_width, outer.is_4state, outer.holds_class_handles,
          outer.nested_queue_levels, outer.element_array_size};
}

ElementQueueShape ShapeOf(const AssocArrayObject& aa) {
  return {aa.elem_width, aa.is_4state, aa.element_queue_handles,
          aa.nested_queue_levels};
}

// §7.4 with Table 7-1: brings `q`, the queue of an element that is a
// fixed-size array of `size` elements, to that many, dropping any past the
// last and filling any missing with the element type's default, x for a
// 4-state element and 0 for a 2-state one.
void FitToFixedSize(QueueObject* q, uint32_t size, Arena& arena) {
  if (size == 0) return;
  if (q->elements.size() > size) q->elements.resize(size);
  while (q->elements.size() < size) {
    q->elements.push_back(q->is_4state
                              ? MakeAllX(arena, q->elem_width)
                              : MakeLogic4VecVal(arena, q->elem_width, 0));
  }
}

// The queue of the shape `shape` gives an element's queue, empty or, for a
// fixed-size array, holding its defaults; where it has levels below it, its
// own elements are queues of one level fewer.
QueueObject* NewElementQueue(const ElementQueueShape& shape, Arena& arena) {
  auto* q = arena.Create<QueueObject>();
  q->elem_width = shape.width;
  q->is_4state = shape.is_4state;
  q->holds_class_handles = shape.handles;
  q->elements_are_queues = shape.levels > 0;
  q->nested_queue_levels = shape.levels > 0 ? shape.levels - 1 : 0;
  FitToFixedSize(q, shape.fixed_size, arena);
  q->AllocateIdsForAppended();
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
    if (!allocate) return NewElementQueue(ShapeOf(*aa), arena);
    entries.data.emplace(key, AssocAllocValue(aa, arena));
    entries.queues.erase(key);
  }
  QueueObject*& q = entries.queues[key];
  if (q == nullptr) q = NewElementQueue(ShapeOf(*aa), arena);
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
  if (q == nullptr) q = NewElementQueue(ShapeOf(*outer), arena);
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
  ElementQueueShape empty = ShapeOf(*outer);
  empty.fixed_size = 0;
  QueueObject* q = NewElementQueue(empty, arena);
  bool listed = item->kind == ExprKind::kConcatenation ||
                (item->kind == ExprKind::kAssignmentPattern &&
                 item->pattern_keys.empty());
  if (listed) {
    for (const Expr* element : item->elements)
      AppendItem(q, element, ctx, arena);
  } else {
    AppendItem(q, item, ctx, arena);
  }
  FitToFixedSize(q, outer->element_array_size, arena);
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

bool TryCopyElementQueueToArray(const Stmt* stmt, const ArrayInfo& dst,
                                SimContext& ctx, Arena& arena) {
  const QueueObject* src =
      ElementQueueOfSelect(stmt->rhs, ctx, arena, /*allocate=*/false);
  if (src == nullptr || dst.is_dynamic || dst.is_queue) return false;
  if (src->elements.size() != dst.size) {
    ctx.GetDiag().Error(stmt->range.start,
                        "array size mismatch in assignment to fixed-size array",
                        Subclause("7.6"));
    return true;
  }
  for (uint32_t i = 0; i < dst.size; ++i) {
    uint32_t index = dst.is_descending ? dst.lo + dst.size - 1 - i : dst.lo + i;
    Variable* element = ctx.FindVariable(std::string(stmt->lhs->text) + "[" +
                                         std::to_string(index) + "]");
    if (element == nullptr) continue;
    element->value = OwnRhsWords(src->elements[i], arena);
    element->NotifyWatchers();
  }
  return true;
}

}  // namespace delta
