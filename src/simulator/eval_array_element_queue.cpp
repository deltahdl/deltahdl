#include "simulator/eval_array_element_queue.h"

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <vector>

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
// (QueueObject::element_array_size, index_lo), and, where that array is
// multidimensional, `inner` its dimensions after the first, which the queues
// one level down are made with (QueueObject::element_inner_dims).
struct ElementQueueShape {
  uint32_t width;
  bool is_4state;
  bool is_signed;
  bool handles;
  uint32_t levels;
  uint32_t fixed_size = 0;
  int64_t fixed_lo = 0;
  bool fixed_descending = false;
  std::vector<FixedDimShape> inner = {};
};

ElementQueueShape ShapeOf(const QueueObject& outer) {
  return {outer.elem_width,          outer.is_4state,
          outer.is_signed,           outer.holds_class_handles,
          outer.nested_queue_levels, outer.element_array_size,
          outer.element_array_lo,    outer.element_array_descending,
          outer.element_inner_dims};
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
  // §7.4.4: the elements of a multidimensional element's queue are the next
  // dimension's arrays, each kept as a queue of that dimension's size.
  if (!shape.inner.empty()) {
    q->element_array_size = shape.inner[0].size;
    q->element_array_lo = shape.inner[0].lo;
    q->element_array_descending = shape.inner[0].descending;
    q->element_inner_dims.assign(shape.inner.begin() + 1, shape.inner.end());
  }
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
  // §7.10 with §10.9.1: where the element's own elements are queues, `a[0]`
  // of `int a[$][$][$]` or of `int q[$][2][2]`, each of its items makes one
  // of those queues in turn.
  if (!FillQueueOfQueues(q, item, ctx, arena)) {
    bool listed = item->kind == ExprKind::kConcatenation ||
                  (item->kind == ExprKind::kAssignmentPattern &&
                   item->pattern_keys.empty());
    if (listed) {
      for (const Expr* element : item->elements)
        AppendItem(q, element, ctx, arena);
    } else {
      AppendItem(q, item, ctx, arena);
    }
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

// The queue of the element at position `pos` of `outer`, an array whose
// elements are queues; null where that element's queue was never made.
static const QueueObject* ElementQueueAt(const QueueObject& outer, size_t pos) {
  auto it = outer.element_queues.find(outer.ElementQueueKeyAt(pos));
  return it == outer.element_queues.end() ? nullptr : it->second;
}

const QueueObject* ElementQueueOrDefault(const QueueObject& outer, size_t pos,
                                         Arena& arena) {
  if (const QueueObject* q = ElementQueueAt(outer, pos)) return q;
  return NewElementQueue(ShapeOf(outer), arena);
}

// A copy of `src`, the queue of one element of an array whose elements are
// queues, made in the shape `shape` gives the target's elements: each value
// owning its words, the element type's fixed size kept, and where the values
// stand for queues of their own, each of those copied one level down. A null
// `src`, an element whose queue was never made, copies as the shape's
// default.
static QueueObject* CopyElementQueue(const QueueObject* src,
                                     const ElementQueueShape& shape,
                                     Arena& arena) {
  if (src == nullptr) return NewElementQueue(shape, arena);
  ElementQueueShape empty = shape;
  empty.fixed_size = 0;
  QueueObject* copy = NewElementQueue(empty, arena);
  for (const Logic4Vec& value : src->elements)
    copy->elements.push_back(OwnRhsWords(value, arena));
  FitToFixedSize(copy, shape.fixed_size, arena);
  copy->AllocateIdsForAppended();
  for (size_t i = 0; copy->elements_are_queues && i < copy->elements.size();
       ++i) {
    copy->element_queues[copy->ElementQueueKeyAt(i)] =
        CopyElementQueue(ElementQueueAt(*src, i), ShapeOf(*copy), arena);
  }
  return copy;
}

// The multidimensional fixed-size array a subarray is copied from, `info`,
// and the context and arena the copy is made in.
struct SubarraySource {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

// §7.12.1 with §7.4.4: a copy of the subarray under `prefix` of the array
// `src` describes, whose first dimension is `dim`, as an element queue of the
// shape `shape` gives the target's elements: the leaves of its last
// dimension as values, and each level above as queues of the level below.
static QueueObject* CopySubarray(const SubarraySource& src,
                                 const std::string& prefix, size_t dim,
                                 const ElementQueueShape& shape) {
  ElementQueueShape empty = shape;
  empty.fixed_size = 0;
  QueueObject* element = NewElementQueue(empty, src.arena);
  ArrayInfo level;
  level.lo = src.info.dim_los[dim];
  level.size = src.info.dim_sizes[dim];
  level.elem_width = src.info.elem_width;
  level.is_4state = src.info.is_4state;
  bool is_last = dim + 1 == src.info.dim_sizes.size();
  for (const Logic4Vec& value :
       CollectVecElements(prefix, level, src.ctx, src.arena)) {
    element->elements.push_back(
        is_last ? OwnRhsWords(SizedForQueueElement(*element, value, src.arena),
                              src.arena)
                : NonexistentQueueElement(element, src.arena));
  }
  FitToFixedSize(element, shape.fixed_size, src.arena);
  element->AllocateIdsForAppended();
  for (uint32_t j = 0; !is_last && j < level.size; ++j) {
    element->element_queues[element->ElementQueueKeyAt(j)] =
        CopySubarray(src, prefix + "[" + std::to_string(level.lo + j) + "]",
                     dim + 1, ShapeOf(*element));
  }
  return element;
}

// §7.12.1 with §7.4.4: `q`, a queue whose elements are fixed-size arrays or
// queues, assigned the elements the locator `rhs` selects of a
// multidimensional array (its subarrays) or of an array whose elements are
// queues (TryCollectLocatorRows), holds one element per selection, each a
// copy of the selected element's values. False, with `q` left alone, where
// `rhs` selects no such elements.
static bool FillQueueFromLocatorRows(QueueObject* q, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
  LocatorRows rows;
  if (!TryCollectLocatorRows(rhs, ctx, arena, rows)) return false;
  ElementQueueShape shape = ShapeOf(*q);
  std::vector<QueueObject*> copies;
  copies.reserve(rows.offsets.size());
  for (uint32_t offset : rows.offsets) {
    if (rows.queue != nullptr) {
      copies.push_back(
          CopyElementQueue(ElementQueueAt(*rows.queue, offset), shape, arena));
      continue;
    }
    std::string subarray = std::string(rows.array_name) + "[" +
                           std::to_string(rows.info->dim_los[0] + offset) + "]";
    copies.push_back(CopySubarray(SubarraySource{*rows.info, ctx, arena},
                                  subarray, 1, shape));
  }
  ResetToPlaceholders(q, copies.size(), arena);
  for (size_t i = 0; i < copies.size(); ++i)
    q->element_queues[q->ElementQueueKeyAt(i)] = copies[i];
  return true;
}

// §7.6 with §7.10: `q`, a queue whose elements are queues, assigned `rhs`
// naming another such queue, holds a copy of each of its elements' queues
// (CopyElementQueue), made before `q` is emptied so that `q = q` keeps what it
// held. False, with `q` left alone, where `rhs` names no such queue.
static bool FillQueueFromQueueOfQueues(QueueObject* q, const Expr* rhs,
                                       SimContext& ctx, Arena& arena) {
  if (rhs->kind != ExprKind::kIdentifier &&
      rhs->kind != ExprKind::kMemberAccess)
    return false;
  const QueueObject* src = FindQueueOfBase(rhs, ctx, arena);
  if (src == nullptr || !src->elements_are_queues) return false;
  std::vector<QueueObject*> copies;
  copies.reserve(src->elements.size());
  for (size_t i = 0; i < src->elements.size(); ++i)
    copies.push_back(
        CopyElementQueue(ElementQueueAt(*src, i), ShapeOf(*q), arena));
  ResetToPlaceholders(q, copies.size(), arena);
  for (size_t i = 0; i < copies.size(); ++i)
    q->element_queues[q->ElementQueueKeyAt(i)] = copies[i];
  return true;
}

// §10.10 with §7.4 and §7.10: `q`, a queue whose elements are queues, assigned
// the unpacked array concatenation `rhs`, holds what each item contributes in
// turn. An item naming an array of `q`'s own type, a queue of the same levels
// and element size, contributes a copy of each of its elements' queues; a
// select of one element of such an array, `r[0]`, a copy of that element's
// queue; and any other item, being of `q`'s element type, one element made as
// a pushed argument makes it (ElementQueueFromItem), so `a` of `int a[3]` is
// one row of `int r[$][3]`. The copies are made before `q` is emptied, so that
// `r = {r, a}` keeps r's rows. False, with `q` left alone, where `rhs` is no
// concatenation.
static bool FillQueueFromConcatenation(QueueObject* q, const Expr* rhs,
                                       SimContext& ctx, Arena& arena) {
  if (rhs->kind != ExprKind::kConcatenation) return false;
  ElementQueueShape shape = ShapeOf(*q);
  std::vector<QueueObject*> copies;
  for (const Expr* item : rhs->elements) {
    if (const QueueObject* element =
            ElementQueueOfSelect(item, ctx, arena, /*allocate=*/false)) {
      copies.push_back(CopyElementQueue(element, shape, arena));
      continue;
    }
    const QueueObject* src = item->kind == ExprKind::kIdentifier ||
                                     item->kind == ExprKind::kMemberAccess
                                 ? FindQueueOfBase(item, ctx, arena)
                                 : nullptr;
    if (src != nullptr && src->elements_are_queues &&
        src->nested_queue_levels == q->nested_queue_levels &&
        src->element_array_size == q->element_array_size) {
      for (size_t i = 0; i < src->elements.size(); ++i)
        copies.push_back(
            CopyElementQueue(ElementQueueAt(*src, i), shape, arena));
      continue;
    }
    copies.push_back(ElementQueueFromItem(q, item, ctx, arena));
  }
  ResetToPlaceholders(q, copies.size(), arena);
  for (size_t i = 0; i < copies.size(); ++i)
    q->element_queues[q->ElementQueueKeyAt(i)] = copies[i];
  return true;
}

void BindElementQueueIterator(const QueueObject& outer, size_t pos,
                              std::string_view iter_name, SimContext& ctx,
                              Arena& arena) {
  const QueueObject* src = ElementQueueAt(outer, pos);
  if (src == nullptr) src = NewElementQueue(ShapeOf(outer), arena);
  QueueObject* item =
      ctx.CreateQueue(iter_name, outer.elem_width, -1, outer.is_4state);
  item->is_signed = outer.is_signed;
  item->index_lo = src->index_lo;
  item->index_descending = src->index_descending;
  item->elements = src->elements;
  item->AllocateIdsForAppended();
}

bool FillQueueOfQueues(QueueObject* q, const Expr* pattern, SimContext& ctx,
                       Arena& arena) {
  if (!q->elements_are_queues) return false;
  if (FillQueueFromLocatorRows(q, pattern, ctx, arena)) return true;
  if (FillQueueFromQueueOfQueues(q, pattern, ctx, arena)) return true;
  if (FillQueueFromConcatenation(q, pattern, ctx, arena)) return true;
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
