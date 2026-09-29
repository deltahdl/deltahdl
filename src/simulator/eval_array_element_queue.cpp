#include "simulator/eval_array_element_queue.h"

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assoc_element.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// What each element's queue of an array whose elements are queues is made
// of: elements of `width` bits, four-state where `is_4state` says so, signed
// where `is_signed` does, class handles where `handles` does, `levels`
// further levels of queues below it (QueueObject::nested_queue_levels), and,
// where the element is a fixed-size array, `fixed_size` elements addressed by
// the bounds `fixed_lo` and `fixed_descending` give
// (QueueObject::element_array_size, index_lo).
struct ElementQueueShape {
  uint32_t width;
  bool is_4state;
  bool is_signed;
  bool handles;
  uint32_t levels;
  uint32_t fixed_size = 0;
  int64_t fixed_lo = 0;
  bool fixed_descending = false;
};

ElementQueueShape ShapeOf(const QueueObject& outer) {
  return {outer.elem_width,          outer.is_4state,
          outer.is_signed,           outer.holds_class_handles,
          outer.nested_queue_levels, outer.element_array_size,
          outer.element_array_lo,    outer.element_array_descending};
}

ElementQueueShape ShapeOf(const AssocArrayObject& aa) {
  return {aa.elem_width, aa.is_4state, aa.is_signed, aa.element_queue_handles,
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
  q->is_signed = shape.is_signed;
  q->holds_class_handles = shape.handles;
  q->elements_are_queues = shape.levels > 0;
  q->nested_queue_levels = shape.levels > 0 ? shape.levels - 1 : 0;
  q->index_lo = shape.fixed_lo;
  q->index_descending = shape.fixed_descending;
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
  QueueObject*& q = outer->element_queues[outer->ElementQueueKeyAt(pos)];
  if (q == nullptr) q = NewElementQueue(ShapeOf(*outer), arena);
  return q;
}

// Appends to `q` what `item` contributes as an item of an unpacked array
// concatenation (§10.10): a queue's elements where it designates one, a copy
// of each element of a fixed-size array variable where it names one (§7.6),
// else its one value, sized to the element type.
void AppendItem(QueueObject* q, const Expr* item, SimContext& ctx,
                Arena& arena) {
  if (const QueueObject* src = FindQueueOfBase(item, ctx, arena)) {
    q->elements.insert(q->elements.end(), src->elements.begin(),
                       src->elements.end());
    return;
  }
  const ArrayInfo* info = item->kind == ExprKind::kIdentifier
                              ? ctx.FindArrayInfo(item->text)
                              : nullptr;
  if (info != nullptr) {
    for (const Logic4Vec& e : CollectVecElements(item->text, *info, ctx, arena))
      q->elements.push_back(
          OwnRhsWords(SizedForQueueElement(*q, e, arena), arena));
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
  // §10.9: a pattern typed with the element's queue type, `T_QI'{2, 3}`,
  // lists the element's items as the bare pattern does.
  item = UnwrapTypedPattern(item);
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

// Empties `q`, a queue whose elements are queues, the element queues with it,
// and gives it `count` placeholder elements with fresh identities, under which
// the caller keeps each element's queue.
static void ResetToPlaceholders(QueueObject* q, size_t count, Arena& arena) {
  q->elements.clear();
  q->element_queues.clear();
  for (size_t i = 0; i < count; ++i)
    q->elements.push_back(NonexistentQueueElement(q, arena));
  q->AssignFreshIds();
}

// §7.12.1 with §7.4.4: `q`, a queue whose elements are fixed-size arrays,
// assigned the rows the locator `rhs` selects of a two-dimensional array
// (TryCollectLocatorRows), holds one element per row, each a copy of the
// row's elements. False, with `q` left alone, where `rhs` selects no rows.
static bool FillQueueFromLocatorRows(QueueObject* q, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
  LocatorRows rows;
  if (!TryCollectLocatorRows(rhs, ctx, arena, rows)) return false;
  ResetToPlaceholders(q, rows.offsets.size(), arena);
  ElementQueueShape empty = ShapeOf(*q);
  empty.fixed_size = 0;
  ArrayInfo row_info;
  row_info.lo = rows.info->dim_los[1];
  row_info.size = rows.info->dim_sizes[1];
  row_info.elem_width = rows.info->elem_width;
  row_info.is_4state = rows.info->is_4state;
  for (size_t i = 0; i < rows.offsets.size(); ++i) {
    std::string row = std::string(rows.array_name) + "[" +
                      std::to_string(rows.info->dim_los[0] + rows.offsets[i]) +
                      "]";
    QueueObject* element = NewElementQueue(empty, arena);
    for (const Logic4Vec& leaf : CollectVecElements(row, row_info, ctx, arena))
      element->elements.push_back(
          OwnRhsWords(SizedForQueueElement(*element, leaf, arena), arena));
    FitToFixedSize(element, q->element_array_size, arena);
    element->AllocateIdsForAppended();
    q->element_queues[q->ElementQueueKeyAt(i)] = element;
  }
  return true;
}

bool FillQueueOfQueues(QueueObject* q, const Expr* pattern, SimContext& ctx,
                       Arena& arena) {
  if (!q->elements_are_queues) return false;
  if (FillQueueFromLocatorRows(q, pattern, ctx, arena)) return true;
  if (pattern->kind != ExprKind::kAssignmentPattern ||
      !pattern->pattern_keys.empty() || pattern->repeat_count != nullptr)
    return false;
  ResetToPlaceholders(q, pattern->elements.size(), arena);
  for (size_t i = 0; i < pattern->elements.size(); ++i) {
    q->element_queues[q->ElementQueueKeyAt(i)] =
        ElementQueueFromItem(q, pattern->elements[i], ctx, arena);
  }
  return true;
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
