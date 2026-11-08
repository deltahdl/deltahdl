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
#include "simulator/assoc_index.h"
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
  return {aa.elem_width,          aa.is_4state,
          aa.is_signed,           aa.element_queue_handles,
          aa.nested_queue_levels, aa.element_array_size,
          aa.element_array_lo,    aa.element_array_descending,
          aa.element_inner_dims};
}

void FitToFixedSize(QueueObject* q, uint32_t size, Arena& arena) {
  if (size == 0) return;
  if (q->elements.size() > size) q->elements.resize(size);
  while (q->elements.size() < size) {
    q->elements.push_back(q->is_4state
                              ? MakeAllX(arena, q->elem_width)
                              : MakeLogic4VecVal(arena, q->elem_width, 0));
  }
}

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

template <typename Key>
struct KeyedEntries {
  std::map<Key, Logic4Vec>& data;
  std::map<Key, QueueObject*>& queues;
};

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

static void WarnAssocElementMiss(const AssocArrayObject* aa, bool present,
                                 const Expr* sel, SimContext& ctx) {
  if (present || aa->has_default) return;
  std::string name;
  BuildLhsName(sel->base, name);
  ctx.GetDiag().Warning(
      sel->index->range.start,
      "associative array '" + name + "': read of non-existent index",
      Subclause("7.8.6"));
}

QueueObject* OfAssocElement(AssocArrayObject* aa, const Expr* sel,
                            SimContext& ctx, Arena& arena, bool allocate) {
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (aa->is_string_key) {
    std::string key = AssocStringKey(idx);
    if (!allocate)
      WarnAssocElementMiss(aa, aa->str_data.count(key) != 0, sel, ctx);
    return AssocElementQueue(
        aa, KeyedEntries<std::string>{aa->str_data, aa->str_element_queues},
        key, allocate, arena);
  }
  if (HasUnknownBits(idx)) return nullptr;
  AssocIndex key =
      AssocIntKey(idx, aa->is_wildcard, aa->index_width, aa->is_index_signed);
  if (!allocate)
    WarnAssocElementMiss(aa, aa->int_data.count(key) != 0, sel, ctx);
  return AssocElementQueue(
      aa, KeyedEntries<AssocIndex>{aa->int_data, aa->int_element_queues}, key,
      allocate, arena);
}

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
  item = UnwrapTypedPattern(item);
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

static void ResetToPlaceholders(QueueObject* q, size_t count, Arena& arena) {
  q->elements.clear();
  q->element_queues.clear();
  for (size_t i = 0; i < count; ++i)
    q->elements.push_back(NonexistentQueueElement(q, arena));
  q->AssignFreshIds();
}

static const QueueObject* ElementQueueAt(const QueueObject& outer, size_t pos) {
  auto it = outer.element_queues.find(outer.ElementQueueKeyAt(pos));
  return it == outer.element_queues.end() ? nullptr : it->second;
}

const QueueObject* ElementQueueOrDefault(const QueueObject& outer, size_t pos,
                                         Arena& arena) {
  if (const QueueObject* q = ElementQueueAt(outer, pos)) return q;
  return NewElementQueue(ShapeOf(outer), arena);
}

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

struct SubarraySource {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

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

static bool FillQueueFromConcatenation(QueueObject* q, const Expr* rhs,
                                       SimContext& ctx, Arena& arena) {
  if (rhs->kind != ExprKind::kConcatenation) return false;
  ElementQueueShape shape = ShapeOf(*q);
  std::vector<QueueObject*> copies;
  for (const Expr* item : rhs->elements) {
    if (const QueueObject* element =
            ElementQueueOfSelect(item, ctx, arena, false)) {
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
  QueueObject* outer =
      allocate ? FindWrittenQueueOfBase(sel->base, ctx, arena, nullptr)
               : FindQueueOfBase(sel->base, ctx, arena);
  if (outer == nullptr || !outer->elements_are_queues) return nullptr;
  return OfQueueElement(outer, sel, ctx, arena);
}

const QueueObject* AssocElementQueueAt(const AssocArrayObject& aa,
                                       const Logic4Vec& key, Arena& arena) {
  const QueueObject* q = nullptr;
  if (aa.is_string_key) {
    auto it = aa.str_element_queues.find(AssocStringKey(key));
    if (it != aa.str_element_queues.end()) q = it->second;
  } else {
    auto it = aa.int_element_queues.find(
        AssocIntKey(key, aa.is_wildcard, aa.index_width, aa.is_index_signed));
    if (it != aa.int_element_queues.end()) q = it->second;
  }
  return q != nullptr ? q : NewElementQueue(ShapeOf(aa), arena);
}

bool SelectsElementQueue(const Expr* sel, SimContext& ctx, Arena& arena) {
  if (sel == nullptr || sel->kind != ExprKind::kSelect ||
      sel->base == nullptr || sel->index == nullptr ||
      sel->index_end != nullptr) {
    return false;
  }
  if (const AssocArrayObject* aa = FindAssocArrayOfBase(sel->base, ctx, arena))
    return aa->elements_are_queues;
  if (sel->base->kind == ExprKind::kIdentifier) {
    const ArrayInfo* info = ctx.FindArrayInfo(sel->base->text);
    if (info != nullptr) return info->elements_are_queues;
  }
  const QueueObject* outer = FindQueueOfBase(sel->base, ctx, arena);
  return outer != nullptr && outer->elements_are_queues;
}

bool TryCopyElementQueueToArray(const Stmt* stmt, const ArrayInfo& dst,
                                SimContext& ctx, Arena& arena) {
  const QueueObject* src = ElementQueueOfSelect(stmt->rhs, ctx, arena, false);
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
