#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_assoc.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_array_internal.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/evaluation.h"
#include "simulator/pattern_type_key.h"
#include "simulator/queue_bound.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz);

uint32_t PatternKeyIndex(const Expr* key, SimContext& ctx, Arena& arena) {
  return static_cast<uint32_t>(EvalExpr(key, ctx, arena).ToUint64());
}

namespace {
struct PatternArrayElem {
  uint32_t idx;
  const ArrayInfo& info;
  const StructTypeInfo* layout = nullptr;
};
}  // namespace

static Logic4Vec FindArrayKeyedValue(const Expr* rhs,
                                     const PatternArrayElem& slot,
                                     SimContext& ctx, Arena& arena) {
  const Expr* item = IndexKeyedItem(rhs, slot.idx, ctx, arena);
  if (item == nullptr)
    item = TypeKeyedItem(rhs, SubjectOfElement(slot.info, ctx), ctx);
  if (item != nullptr) return EvalExpr(item, ctx, arena);
  if (slot.layout != nullptr && PatternHasTypeKey(rhs, ctx))
    return EvalStructPatternValue(rhs, slot.layout, ctx, arena);
  if (const Expr* fallback = DefaultKeyedItem(rhs))
    return EvalDefaultForElement(fallback, slot.layout, ctx, arena);
  return slot.info.is_4state ? MakeAllX(arena, slot.info.elem_width)
                             : MakeLogic4VecVal(arena, slot.info.elem_width, 0);
}

namespace {
struct PatternDist {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
  const StructTypeInfo* layout;
};
}  // namespace

static const Expr* SelectDimElement(const Expr* pat, uint32_t idx, uint32_t pos,
                                    const PatternDist& pd) {
  if (pat->pattern_keys.empty()) {
    if (pat->elements.size() == 1 && pat->elements[0]->is_pattern_replication) {
      const auto& body = pat->elements[0]->elements;
      return body.empty() ? nullptr : body[pos % body.size()];
    }
    return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
  }
  if (const Expr* item = IndexKeyedItem(pat, idx, pd.ctx, pd.arena))
    return item;
  if (const Expr* item =
          TypeKeyedItem(pat, SubjectOfElement(pd.info, pd.ctx), pd.ctx))
    return item;
  return DefaultKeyedItem(pat);
}

static void WriteLeaf(const PatternDist& pd, const std::string& name,
                      const Expr* sub) {
  auto* elem = pd.ctx.FindVariable(name);
  if (!elem) return;
  Logic4Vec val = sub ? EvalItemForLayout(sub, pd.layout, pd.ctx, pd.arena)
                      : MakeLogic4VecVal(pd.arena, pd.info.elem_width, 0);
  elem->value =
      OwnRhsWords(ResizeToWidth(val, pd.info.elem_width, pd.arena), pd.arena);
  elem->NotifyWatchers();
}

static void WriteScalarSubtree(const PatternDist& pd, const std::string& prefix,
                               size_t d, const Expr* sub) {
  uint32_t lo = pd.info.dim_los[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  for (uint32_t i = 0; i < pd.info.dim_sizes[d]; ++i) {
    std::string child = prefix + "[" + std::to_string(lo + i) + "]";
    if (last)
      WriteLeaf(pd, child, sub);
    else
      WriteScalarSubtree(pd, child, d + 1, sub);
  }
}

static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat);

static void DistributeSubarrayItem(const PatternDist& pd,
                                   const std::string& prefix, size_t d,
                                   const Expr* sub) {
  if (sub == nullptr) {
    WriteScalarSubtree(pd, prefix, d, sub);
    return;
  }
  if (sub->kind == ExprKind::kConcatenation) {
    DistributeConcatToSubarray({pd.info, prefix, d}, sub, pd.ctx, pd.arena);
    return;
  }
  const Expr* pattern = sub->kind == ExprKind::kAssignmentPattern
                            ? sub
                            : TypedUnpackedArrayPattern(sub, pd.ctx);
  if (pattern != nullptr) {
    DistributeDimPattern(pd, prefix, d, pattern);
    return;
  }
  if (!CopyArrayItemToSubarray({pd.info, prefix, d}, sub, pd.ctx, pd.arena))
    WriteScalarSubtree(pd, prefix, d, sub);
}

static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat) {
  uint32_t lo = pd.info.dim_los[d];
  uint32_t size = pd.info.dim_sizes[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  bool descending = pd.info.dim_descending[d];
  for (uint32_t i = 0; i < size; ++i) {
    std::string child = prefix + "[" + std::to_string(lo + i) + "]";
    const Expr* sub =
        SelectDimElement(pat, lo + i, descending ? (size - 1 - i) : i, pd);
    if (last)
      WriteLeaf(pd, child, sub);
    else
      DistributeSubarrayItem(pd, child, d + 1, sub);
  }
}

Logic4Vec PatternItemAt(const Expr* rhs, const ArrayPatternTarget& target,
                        uint32_t i, SimContext& ctx, Arena& arena) {
  const ArrayInfo& info = target.info;
  bool replicate =
      rhs->elements.size() == 1 && rhs->elements[0]->is_pattern_replication;
  uint32_t inner_count =
      replicate ? static_cast<uint32_t>(rhs->elements[0]->elements.size()) : 0;
  if (!rhs->pattern_keys.empty()) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    PatternArrayElem slot{idx, info, target.layout};
    return FindArrayKeyedValue(rhs, slot, ctx, arena);
  }
  if (replicate && inner_count > 0) {
    return EvalItemForLayout(rhs->elements[0]->elements[i % inner_count],
                             target.layout, ctx, arena);
  }
  if (i < rhs->elements.size())
    return EvalItemForLayout(rhs->elements[i], target.layout, ctx, arena);
  return MakeLogic4VecVal(arena, info.elem_width, 0);
}

void DistributePatternToArray(std::string_view arr_name, const ArrayInfo& info,
                              const Expr* rhs, SimContext& ctx, Arena& arena) {
  if (info.dim_sizes.size() > 1) {
    DistributeDimPattern(
        PatternDist{info, ctx, arena, StructLayoutOfName(arr_name, ctx)},
        std::string(arr_name), 0, rhs);
    return;
  }
  const ArrayPatternTarget kTarget{info, StructLayoutOfName(arr_name, ctx)};
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    Logic4Vec val = PatternItemAt(rhs, kTarget, i, ctx, arena);
    elem->value =
        OwnRhsWords(ResizeToWidth(val, info.elem_width, arena), arena);
    elem->NotifyWatchers();
  }
}

static const Expr* AsArrayConcatPattern(const Expr* item, SimContext& ctx) {
  if (item->kind == ExprKind::kAssignmentPattern) return item;
  return UnpackedArrayTypedPattern(item, ctx);
}

static void OwnConcatElements(std::vector<Logic4Vec>& elems, Arena& arena) {
  for (auto& elem : elems) elem = OwnRhsWords(elem, arena);
}

static void CollectArrayLeaves(std::string_view name, const ArrayInfo& ai,
                               SimContext& ctx, std::vector<Logic4Vec>& out) {
  for (uint32_t k = 0; k < ArrayElementCount(ai); ++k) {
    auto* v = ctx.FindVariable(std::string(name) + ArrayElementSuffixAt(ai, k));
    if (v) out.push_back(v->value);
  }
}

static bool CollectNamedArrayElements(const Expr* item, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  if (item->kind != ExprKind::kIdentifier) return false;
  if (auto* ai = ctx.FindArrayInfo(item->text)) {
    CollectArrayLeaves(item->text, *ai, ctx, out);
    return true;
  }
  auto* q = ctx.FindQueue(item->text);
  if (q == nullptr) return false;
  out.insert(out.end(), q->elements.begin(), q->elements.end());
  return true;
}

bool CollectArrayItemElements(const Expr* item, SimContext& ctx, Arena& arena,
                              std::vector<Logic4Vec>& out) {
  if (CollectNamedArrayElements(item, ctx, out)) return true;
  if (item->kind != ExprKind::kSelect) return false;
  if (CollectUnpackedSliceElements(item, ctx, arena, out)) return true;
  std::string prefix;
  ArrayInfo sub;
  if (!ResolveSubarraySelect(item, ctx, arena, prefix, sub)) return false;
  CollectArrayLeaves(prefix, sub, ctx, out);
  return true;
}

std::vector<Logic4Vec> CollectConcatElements(const Expr* rhs, SimContext& ctx,
                                             Arena& arena) {
  std::vector<Logic4Vec> elems;
  for (auto* item : rhs->elements) {
    if (CollectNamedArrayElements(item, ctx, elems)) continue;
    if (const Expr* pat = AsArrayConcatPattern(item, ctx)) {
      for (auto* elem : pat->elements) {
        elems.push_back(EvalExpr(elem, ctx, arena));
      }
      continue;
    }
    if (item->kind == ExprKind::kSelect &&
        CollectUnpackedSliceElements(item, ctx, arena, elems)) {
      continue;
    }
    elems.push_back(EvalExpr(item, ctx, arena));
  }
  return elems;
}

void DistributeConcatToArray(std::string_view arr_name, const ArrayInfo& info,
                             const Expr* rhs, SimContext& ctx, Arena& arena) {
  auto elems = CollectConcatElements(rhs, ctx, arena);
  OwnConcatElements(elems, arena);
  uint32_t count = ArrayElementCount(info);
  if (elems.size() != count) {
    ctx.GetDiag().Error(
        rhs->range.start,
        "unpacked array concatenation size mismatch: expected " +
            std::to_string(count) + " elements, got " +
            std::to_string(elems.size()),
        Subclause("10.10"));
    return;
  }
  for (uint32_t i = 0; i < count; ++i) {
    auto name = std::string(arr_name) + ArrayElementSuffixAt(info, i);
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    elem->value = ResizeToWidth(elems[i], info.elem_width, arena);
    elem->NotifyWatchers();
  }
}

static void CopyResizableSourceToArray(std::string_view dst_name,
                                       const ArrayInfo& dst,
                                       const QueueObject& src_q,
                                       uint32_t src_size, SimContext& ctx) {
  uint32_t n = std::min(dst.size, src_size);
  for (uint32_t i = 0; i < n; ++i) {
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto dn = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* dv = ctx.FindVariable(dn);
    if (dv) {
      dv->value = OwnRhsWords(src_q.elements[i], ctx.GetArena());
      dv->NotifyWatchers();
    }
  }
}

static bool TryArrayIdentifierCopy(const Stmt* stmt, SimContext& ctx,
                                   bool* handled) {
  *handled = false;
  auto* dst = ctx.FindArrayInfo(stmt->lhs->text);
  if (!dst) return false;
  *handled = true;
  auto* src = ctx.FindArrayInfo(stmt->rhs->text);
  auto* src_q = ctx.FindQueue(stmt->rhs->text);
  bool src_is_aggregate = (src != nullptr) || (src_q != nullptr);
  if (!src_is_aggregate) return false;
  bool src_resizable = src_q != nullptr;
  uint32_t src_size =
      src_resizable ? static_cast<uint32_t>(src_q->elements.size()) : src->size;

  if (!dst->is_dynamic && !dst->is_queue && src_resizable &&
      dst->size != src_size) {
    ctx.GetDiag().Error(stmt->range.start,
                        "array size mismatch in assignment to fixed-size array",
                        Subclause("7.6"));
    return true;
  }
  if (src_resizable) {
    CopyResizableSourceToArray(stmt->lhs->text, *dst, *src_q, src_size, ctx);
    return true;
  }
  CopyArrayElements(stmt->lhs->text, *dst, stmt->rhs->text, *src, ctx);
  return true;
}

static bool TryArraySliceCopy(const Stmt* stmt, std::string_view dst_name,
                              const ArrayInfo& dst, SimContext& ctx,
                              Arena& arena) {
  std::vector<Logic4Vec> src;
  if (!CollectUnpackedSliceElements(stmt->rhs, ctx, arena, src)) return false;
  for (uint32_t i = 0; i < dst.size && i < src.size(); ++i) {
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto name = std::string(dst_name) + "[" + std::to_string(di) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    elem->value = ResizeToWidth(src[i], dst.elem_width, arena);
    elem->NotifyWatchers();
  }
  return true;
}

bool TryArrayAggregateAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs) return false;
  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  if (ainfo && stmt->rhs->kind == ExprKind::kAssignmentPattern) {
    DistributePatternToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
    return true;
  }
  if (ainfo && stmt->rhs->kind == ExprKind::kConcatenation) {
    DistributeConcatToArray(stmt->lhs->text, *ainfo, stmt->rhs, ctx, arena);
    return true;
  }
  return false;
}

bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier || !stmt->rhs) return false;
  auto* ainfo = ctx.FindArrayInfo(stmt->lhs->text);
  if (ainfo && stmt->rhs->kind == ExprKind::kSelect &&
      (TryCopyElementQueueToArray(stmt, *ainfo, ctx, arena) ||
       TryArraySliceCopy(stmt, stmt->lhs->text, *ainfo, ctx, arena))) {
    return true;
  }
  if (ainfo && TryFillArrayFromValue(stmt, *ainfo, ctx, arena)) return true;
  if (stmt->rhs->kind == ExprKind::kIdentifier) {
    bool handled = false;
    bool result = TryArrayIdentifierCopy(stmt, ctx, &handled);
    if (handled) return result;
  }
  return false;
}

static Logic4Vec SizedAssocElementValue(const Expr* base,
                                        const AssocArrayObject* aa,
                                        const Logic4Vec& rhs_val,
                                        SimContext& ctx, Arena& arena) {
  const bool kDeclared = base->kind == ExprKind::kIdentifier &&
                         ctx.FindAssocArray(base->text) == aa;
  if (kDeclared || rhs_val.is_string || rhs_val.is_real) return rhs_val;
  return ResizeToWidth(rhs_val, aa->elem_width, arena);
}

static void AnnounceAssocElementWrite(const Expr* base, ClassObject* owner,
                                      SimContext& ctx) {
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
  } else if (base->kind == ExprKind::kIdentifier) {
    NotifyOwningVar(ctx, base->text);
  }
}

bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena) {
  if (!lhs->base || !lhs->index) return false;
  ClassObject* owner = nullptr;
  auto* aa = ElementAssocOfSelect(lhs->base, ctx, arena, true);
  if (aa == nullptr) aa = FindAssocArrayOfBase(lhs->base, ctx, arena, &owner);
  if (!aa) return false;
  Logic4Vec stored = SizedAssocElementValue(lhs->base, aa, rhs_val, ctx, arena);
  if (aa->is_string_key) {
    auto key = AssocStringKey(EvalExpr(lhs->index, ctx, arena));
    auto driven = aa->str_drives.find(key);
    if (driven != aa->str_drives.end() && driven->second.Drives()) return true;
    aa->str_data[key] = stored;
  } else {
    auto key_val = EvalExpr(lhs->index, ctx, arena);
    if (HasUnknownBits(key_val)) {
      ctx.GetDiag().Warning(lhs->index->range.start,
                            "associative array index contains x/z",
                            Subclause("7.8.6"));
      return true;
    }
    auto key = AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                           aa->is_index_signed);
    auto driven = aa->int_drives.find(key);
    if (driven != aa->int_drives.end() && driven->second.Drives()) return true;
    aa->int_data[key] = stored;
  }
  AnnounceAssocElementWrite(lhs->base, owner, ctx);
  return true;
}

bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena&) {
  if (!lhs->base || !lhs->index) return false;
  auto& arena = ctx.GetArena();
  ClassObject* owner = nullptr;
  auto* q = FindWrittenQueueOfBase(lhs->base, ctx, arena, &owner);
  if (!q) return false;
  bool idx_xz = false;
  auto idx = EvalQueueIndex(lhs->index, q, ctx, arena, &idx_xz);

  if (idx_xz) {
    ctx.GetDiag().Warning(lhs->index->range.start,
                          "queue write index contains x/z",
                          Subclause("7.10.1"));
    return true;
  }
  auto sz = static_cast<int64_t>(q->elements.size());

  if (idx == sz) {
    q->elements.push_back(SizedForQueueElement(*q, rhs_val, arena));
    q->element_ids.push_back(q->AllocateId());
    ++q->generation;
    EnforceQueueBound(q, "indexed write", lhs->range.start, ctx);
    AnnounceQueueChange(lhs->base, owner, ctx);
    return true;
  }
  if (idx >= 0 && idx < sz) {
    if (q->ElementIsDriven(static_cast<size_t>(idx))) return true;
    q->elements[static_cast<size_t>(idx)] =
        SizedForQueueElement(*q, rhs_val, arena);
    AnnounceQueueChange(lhs->base, owner, ctx);
    return true;
  }

  ctx.GetDiag().Warning(lhs->index->range.start,
                        "queue write index out of bounds", Subclause("7.10.1"));
  return true;
}

static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz = nullptr) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  int64_t last =
      q->elements.empty() ? 0 : static_cast<int64_t>(q->elements.size()) - 1;
  dv->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(last));
  auto val = EvalExpr(expr, ctx, arena);
  ctx.PopScope();
  if (has_xz) *has_xz = HasUnknownBits(val);
  uint64_t raw = val.ToUint64();
  if (val.width > 0 && val.width < 64) {
    uint64_t sign = uint64_t{1} << (val.width - 1);
    if (raw & sign) raw |= ~uint64_t{0} << val.width;
  }
  return q->PositionOf(static_cast<int64_t>(raw));
}

int64_t QueueElementIndex(const Expr* index, QueueObject* q, SimContext& ctx,
                          Arena& arena, bool* has_xz) {
  return EvalQueueIndex(index, q, ctx, arena, has_xz);
}

static bool CollectFromQueueSlice(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || !expr->index_end)
    return false;
  auto* q = FindQueueOfBase(expr->base, ctx, arena);
  if (!q) return false;
  bool lo_xz = false, hi_xz = false;
  auto lo = EvalQueueIndex(expr->index, q, ctx, arena, &lo_xz);
  auto hi = EvalQueueIndex(expr->index_end, q, ctx, arena, &hi_xz);

  if (lo_xz || hi_xz) return true;

  if (lo < 0) lo = 0;
  auto qsz = static_cast<int64_t>(q->elements.size());

  if (hi >= qsz) hi = qsz - 1;

  for (int64_t i = lo; i <= hi; ++i)
    out.push_back(q->elements[static_cast<size_t>(i)]);
  return true;
}

static bool CollectFromQueueElem(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || expr->index_end)
    return false;
  auto* q = FindQueueOfBase(expr->base, ctx, arena);
  if (!q) return false;
  bool idx_xz = false;
  auto idx = EvalQueueIndex(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz || idx < 0 || static_cast<size_t>(idx) >= q->elements.size())
    out.push_back(NonexistentQueueElement(q, arena));
  else
    out.push_back(q->elements[static_cast<size_t>(idx)]);
  return true;
}

void CollectFixedArrayElements(std::string_view name, const ArrayInfo& ai,
                               SimContext& ctx, std::vector<Logic4Vec>& out) {
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.is_descending ? (ai.lo + ai.size - 1 - i) : (ai.lo + i);
    auto ename = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(ename);
    if (v) out.push_back(v->value);
  }
}

static void CollectQueueItem(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  if (CollectFromQueueSlice(expr, ctx, arena, out)) return;
  if (const QueueObject* element =
          ElementQueueOfSelect(expr, ctx, arena, false)) {
    out.insert(out.end(), element->elements.begin(), element->elements.end());
    return;
  }
  if (CollectFromQueueElem(expr, ctx, arena, out)) return;
  if (const Expr* pattern = UnpackedArrayTypedPattern(expr, ctx)) {
    for (auto* item : pattern->elements)
      out.push_back(EvalExpr(item, ctx, arena));
    return;
  }
  if (expr->kind == ExprKind::kIdentifier ||
      expr->kind == ExprKind::kMemberAccess) {
    auto* q = FindQueueOfBase(expr, ctx, arena);
    if (q) {
      out.insert(out.end(), q->elements.begin(), q->elements.end());
      return;
    }
  }
  if (expr->kind == ExprKind::kIdentifier) {
    auto* ai = ctx.FindArrayInfo(expr->text);
    if (ai) {
      CollectFixedArrayElements(expr->text, *ai, ctx, out);
      return;
    }
  }
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  if (CollectUnpackedSliceElements(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

static bool IsPositionalPattern(const Expr* expr) {
  if (expr->kind != ExprKind::kAssignmentPattern) return false;
  if (!expr->pattern_keys.empty() || expr->elements.empty()) return false;
  return expr->elements.size() != 1 ||
         !expr->elements[0]->is_pattern_replication;
}

void CollectQueueElements(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::vector<Logic4Vec>& out) {
  if (expr->kind == ExprKind::kConcatenation || IsPositionalPattern(expr)) {
    for (auto* elem : expr->elements) CollectQueueItem(elem, ctx, arena, out);
    return;
  }
  CollectQueueItem(expr, ctx, arena, out);
}

static void CopyNewInit(const Expr* rhs, QueueObject* q,
                        const std::vector<Logic4Vec>& saved, SimContext& ctx,
                        Arena& arena) {
  if (rhs->args.size() < 2) return;
  auto* init_expr = rhs->args[1];
  if (!init_expr) return;
  std::vector<Logic4Vec> collected;
  const bool kSelf = init_expr->kind == ExprKind::kIdentifier &&
                     ctx.FindQueue(init_expr->text) == q;
  if (!kSelf) CollectQueueElements(init_expr, ctx, arena, collected);
  const auto& src_elems = kSelf ? saved : collected;
  size_t copy_len = std::min(q->elements.size(), src_elems.size());
  for (size_t i = 0; i < copy_len; ++i)
    q->elements[i] = OwnRhsWords(src_elems[i], arena);
}

static QueueObject* QueueOfAssignTarget(const Expr* lhs, SimContext& ctx,
                                        Arena& arena, ClassObject** owner) {
  if (lhs->kind == ExprKind::kSelect) {
    return ElementQueueOfSelect(lhs, ctx, arena, true);
  }
  if (lhs->kind != ExprKind::kIdentifier &&
      lhs->kind != ExprKind::kMemberAccess) {
    return nullptr;
  }
  return FindWrittenQueueOfBase(lhs, ctx, arena, owner);
}

bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  ClassObject* owner = nullptr;
  auto* q = QueueOfAssignTarget(stmt->lhs, ctx, arena, &owner);
  if (!q) return false;
  if (stmt->rhs->kind == ExprKind::kConcatenation &&
      stmt->rhs->elements.empty()) {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    AnnounceQueueChange(stmt->lhs, owner, ctx);
    return true;
  }
  if (stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new" &&
      !stmt->rhs->args.empty()) {
    auto sz_val = EvalExpr(stmt->rhs->args[0], ctx, arena);
    int64_t sz = LongintValue(sz_val);

    if (sz < 0) {
      ctx.GetDiag().Error(stmt->rhs->args[0]->range.start,
                          "dynamic array new[] size is negative",
                          Subclause("7.5.1"));
      return true;
    }

    auto saved = q->elements;
    const bool kFillX = q->is_4state && !q->holds_class_handles &&
                        !q->elements_are_queues && q->elem_width > 0;
    q->elements.clear();
    q->elements.reserve(static_cast<size_t>(sz));
    for (int64_t i = 0; i < sz; ++i)
      q->elements.push_back(kFillX ? MakeAllX(arena, q->elem_width)
                                   : MakeLogic4VecVal(arena, q->elem_width, 0));
    CopyNewInit(stmt->rhs, q, saved, ctx, arena);
    EnforceQueueBound(q, "new[]", stmt->rhs->range.start, ctx);
    q->AssignFreshIds();
    ++q->generation;
    AnnounceQueueChange(stmt->lhs, owner, ctx);
    return true;
  }
  if (!FillQueueOfQueues(q, UnwrapTypedPattern(stmt->rhs), ctx, arena)) {
    std::vector<Logic4Vec> elems;
    CollectQueueElements(stmt->rhs, ctx, arena, elems);
    SizeAndOwnQueueElements(*q, elems, arena);
    q->elements = std::move(elems);
    q->AssignFreshIds();
  }
  EnforceQueueBound(q, "assignment", stmt->rhs->range.start, ctx);
  ++q->generation;
  AnnounceQueueChange(stmt->lhs, owner, ctx);
  return true;
}

}  // namespace delta
