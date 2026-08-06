#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// Defined below; forward-declared so the queue-write helpers above its
// definition can call it. The default argument lives on the definition.
static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz);

uint32_t PatternKeyIndex(const Expr* key, SimContext& ctx, Arena& arena) {
  return static_cast<uint32_t>(EvalExpr(key, ctx, arena).ToUint64());
}

bool IsTypeKeyword(std::string_view key) {
  return key == "int" || key == "integer" || key == "logic" || key == "reg" ||
         key == "byte" || key == "shortint" || key == "longint" ||
         key == "bit" || key == "real" || key == "shortreal" || key == "time" ||
         key == "realtime" || key == "string";
}

bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kInt:
      return key == "int";
    case DataTypeKind::kInteger:
      return key == "integer";
    case DataTypeKind::kLogic:
      return key == "logic";
    case DataTypeKind::kReg:
      return key == "reg";
    case DataTypeKind::kByte:
      return key == "byte";
    case DataTypeKind::kShortint:
      return key == "shortint";
    case DataTypeKind::kLongint:
      return key == "longint";
    case DataTypeKind::kBit:
      return key == "bit";
    case DataTypeKind::kReal:
      return key == "real";
    case DataTypeKind::kShortreal:
      return key == "shortreal";
    case DataTypeKind::kTime:
      return key == "time";
    case DataTypeKind::kRealtime:
      return key == "realtime";
    case DataTypeKind::kString:
      return key == "string";
    default:
      return false;
  }
}

// Finds the pattern element whose explicit integer key equals idx. Returns the
// matching element index, or rhs->elements.size() when none matches.
static size_t FindIndexKeyedElement(const Expr* rhs, uint32_t idx,
                                    SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    const auto* key = rhs->pattern_keys[i];
    if (key->text == "default" || IsTypeKeyword(key->text)) continue;
    if (PatternKeyIndex(key, ctx, arena) == idx) return i;
  }
  return rhs->elements.size();
}

// Finds the pattern element keyed by a type keyword matching elem_type. Returns
// the matching element index, or rhs->elements.size() when none matches.
static size_t FindTypeKeyedElement(const Expr* rhs, DataTypeKind elem_type) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    auto key = rhs->pattern_keys[i]->text;
    if (IsTypeKeyword(key) && TypeKeyMatchesKind(key, elem_type)) return i;
  }
  return rhs->elements.size();
}

// Finds the pattern element keyed by "default". Returns the matching element
// index, or rhs->elements.size() when none matches.
static size_t FindDefaultKeyedElement(const Expr* rhs) {
  for (size_t i = 0; i < rhs->pattern_keys.size(); ++i) {
    if (i >= rhs->elements.size()) break;
    if (rhs->pattern_keys[i]->text == "default") return i;
  }
  return rhs->elements.size();
}

// One element slot of the unpacked-array target of an assignment pattern
// (IEEE 1800 §7.6 / §10.9.2). `idx` is the array index being filled; `width`
// and `elem_type_kind` mirror the element-type fields of the target's
// ArrayInfo and select default/type-keyed pattern members.
namespace {
struct PatternArrayElem {
  uint32_t idx;
  uint32_t width;
  DataTypeKind elem_type_kind;
};
}  // namespace

static Logic4Vec FindArrayKeyedValue(const Expr* rhs,
                                     const PatternArrayElem& slot,
                                     SimContext& ctx, Arena& arena) {
  size_t match = FindIndexKeyedElement(rhs, slot.idx, ctx, arena);
  if (match >= rhs->elements.size())
    match = FindTypeKeyedElement(rhs, slot.elem_type_kind);
  if (match >= rhs->elements.size()) match = FindDefaultKeyedElement(rhs);
  if (match < rhs->elements.size())
    return EvalExpr(rhs->elements[match], ctx, arena);
  return MakeLogic4VecVal(arena, slot.width, 0);
}

namespace {
// §7.4.2: bundle for distributing a (possibly nested) assignment pattern into a
// fixed multidimensional unpacked array, keeping the recursive walk within the
// parameter-count limit.
struct PatternDist {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// §10.9.1: the pattern element that fills one dimension's element at index
// `idx` (position `pos`): a positional element, an index-keyed element, or the
// default-keyed element. Null when the pattern supplies none for this element.
static const Expr* SelectDimElement(const Expr* pat, uint32_t idx, uint32_t pos,
                                    const PatternDist& pd) {
  if (pat->pattern_keys.empty()) {
    // §10.9.1: a replication in an array pattern stands for an entire single
    // dimension. Expand its body positionally across this dimension so each of
    // the N copies lands on successive elements (e.g. '{2{'{3{y}}}} fills a
    // [_:_][_:_] array with y at every leaf) instead of leaking the replicate
    // node out as one scalar.
    if (pat->elements.size() == 1 &&
        pat->elements[0]->kind == ExprKind::kReplicate) {
      const auto& body = pat->elements[0]->elements;
      return body.empty() ? nullptr : body[pos % body.size()];
    }
    return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
  }
  size_t m = FindIndexKeyedElement(pat, idx, pd.ctx, pd.arena);
  if (m >= pat->elements.size()) m = FindDefaultKeyedElement(pat);
  return m < pat->elements.size() ? pat->elements[m] : nullptr;
}

// Writes one scalar leaf element (resizing/defaulting to the element width).
static void WriteLeaf(const PatternDist& pd, const std::string& name,
                      const Expr* sub) {
  auto* elem = pd.ctx.FindVariable(name);
  if (!elem) return;
  Logic4Vec val = sub ? EvalExpr(sub, pd.ctx, pd.arena)
                      : MakeLogic4VecVal(pd.arena, pd.info.elem_width, 0);
  elem->value = ResizeToWidth(val, pd.info.elem_width, pd.arena);
  elem->NotifyWatchers();
}

// §10.9.1: broadcasts one scalar `sub` to every leaf at and below dimension `d`
// of the subtree rooted at `prefix` (an inner default that is not itself a
// nested pattern fills the whole sub-array).
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

// §7.4.2/§10.9.1: distribute the assignment pattern `pat` across dimension `d`
// of the subtree rooted at `prefix`. A nested pattern recurses into the next
// dimension; a scalar at a non-last dimension broadcasts to the sub-array.
static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat) {
  uint32_t lo = pd.info.dim_los[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  for (uint32_t i = 0; i < pd.info.dim_sizes[d]; ++i) {
    std::string child = prefix + "[" + std::to_string(lo + i) + "]";
    const Expr* sub = SelectDimElement(pat, lo + i, i, pd);
    bool is_pattern = sub && (sub->kind == ExprKind::kAssignmentPattern ||
                              sub->kind == ExprKind::kConcatenation);
    if (last)
      WriteLeaf(pd, child, sub);
    else if (is_pattern)
      DistributeDimPattern(pd, child, d + 1, sub);
    else
      WriteScalarSubtree(pd, child, d + 1, sub);
  }
}

static void DistributePatternToArray(std::string_view arr_name,
                                     const ArrayInfo& info, const Expr* rhs,
                                     SimContext& ctx, Arena& arena) {
  if (info.dim_sizes.size() > 1) {
    DistributeDimPattern(PatternDist{info, ctx, arena}, std::string(arr_name),
                         0, rhs);
    return;
  }
  bool named = !rhs->pattern_keys.empty();
  bool replicate = rhs->elements.size() == 1 &&
                   rhs->elements[0]->kind == ExprKind::kReplicate;
  uint32_t inner_count =
      replicate ? static_cast<uint32_t>(rhs->elements[0]->elements.size()) : 0;
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    if (named) {
      PatternArrayElem slot{idx, info.elem_width, info.elem_type_kind};
      elem->value = ResizeToWidth(FindArrayKeyedValue(rhs, slot, ctx, arena),
                                  info.elem_width, arena);
    } else if (replicate && inner_count > 0) {
      auto val =
          EvalExpr(rhs->elements[0]->elements[i % inner_count], ctx, arena);
      elem->value = ResizeToWidth(val, info.elem_width, arena);
    } else if (i < rhs->elements.size()) {
      auto val = EvalExpr(rhs->elements[i], ctx, arena);
      elem->value = ResizeToWidth(val, info.elem_width, arena);
    } else {
      elem->value = MakeLogic4VecVal(arena, info.elem_width, 0);
    }
    elem->NotifyWatchers();
  }
}

static void CollectFixedArrayElements(std::string_view name,
                                      const ArrayInfo& ai, SimContext& ctx,
                                      std::vector<Logic4Vec>& out);

// §10.10: an element of an unpacked array concatenation may itself be an
// assignment pattern that contributes its elements (not a single value),
// either bare ('{...}) or typed (AI3'{5, 6, 7}). The typed form parses as a
// cast wrapping the pattern, so unwrap it here.
static const Expr* AsArrayConcatPattern(const Expr* item) {
  if (item->kind == ExprKind::kAssignmentPattern) return item;
  if (item->kind == ExprKind::kCast && item->lhs &&
      item->lhs->kind == ExprKind::kAssignmentPattern)
    return item->lhs;
  return nullptr;
}

static std::vector<Logic4Vec> CollectConcatElements(const Expr* rhs,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  std::vector<Logic4Vec> elems;
  for (auto* item : rhs->elements) {
    if (item->kind == ExprKind::kIdentifier) {
      auto* ai = ctx.FindArrayInfo(item->text);
      if (ai) {
        CollectFixedArrayElements(item->text, *ai, ctx, elems);
        continue;
      }
      auto* q = ctx.FindQueue(item->text);
      if (q) {
        elems.insert(elems.end(), q->elements.begin(), q->elements.end());
        continue;
      }
    }
    if (const Expr* pat = AsArrayConcatPattern(item)) {
      for (auto* elem : pat->elements) {
        elems.push_back(EvalExpr(elem, ctx, arena));
      }
      continue;
    }
    elems.push_back(EvalExpr(item, ctx, arena));
  }
  return elems;
}

static void DistributeConcatToArray(std::string_view arr_name,
                                    const ArrayInfo& info, const Expr* rhs,
                                    SimContext& ctx, Arena& arena) {
  auto elems = CollectConcatElements(rhs, ctx, arena);
  if (elems.size() != info.size) {
    ctx.GetDiag().Error(
        {},
        "unpacked array concatenation size mismatch: expected " +
            std::to_string(info.size) + " elements, got " +
            std::to_string(elems.size()),
        Subclause::Unread());
    return;
  }
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    elem->value = ResizeToWidth(elems[i], info.elem_width, arena);
    elem->NotifyWatchers();
  }
}

// Copies the resizable (queue) source elements into the fixed/dynamic array
// destination dst named dst_name, element by element.
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
      dv->value = src_q.elements[i];
      dv->NotifyWatchers();
    }
  }
}

// Handles "array = identifier" where the destination names an array. Sets
// *handled to true and returns true/false matching the caller's return value
// when the destination is an array; leaves *handled false (fall through) when
// the destination is not an array.
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
    ctx.GetDiag().Error({},
                        "array size mismatch in assignment to fixed-size array",
                        Subclause::Unread());
    return true;
  }
  if (src_resizable) {
    CopyResizableSourceToArray(stmt->lhs->text, *dst, *src_q, src_size, ctx);
    return true;
  }
  CopyArrayElements(stmt->lhs->text, *dst, stmt->rhs->text, *src, ctx);
  return true;
}

// §7.4.5: copies a slice of an unpacked array into an array, as in the clause's
// own `busB = busA[7:6];` -- the slice names two elements and the destination
// holds them as two elements, rather than as the one value their concatenation
// would make. §7.6 pairs the two by position -- "Correspondence between
// elements is determined by the left-to-right order of elements in each array"
// -- so the slice arrives in the source array's declared order and is written
// in the destination's, leaving `busB[1]` holding `busA[7]` whichever way each
// of the two was declared.
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

bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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
  if (ainfo && stmt->rhs->kind == ExprKind::kSelect &&
      TryArraySliceCopy(stmt, stmt->lhs->text, *ainfo, ctx, arena)) {
    return true;
  }
  if (stmt->rhs->kind == ExprKind::kIdentifier) {
    bool handled = false;
    bool result = TryArrayIdentifierCopy(stmt, ctx, &handled);
    if (handled) return result;
  }
  return false;
}

bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (!aa || !lhs->index) return false;
  if (aa->is_string_key) {
    auto key_vec = EvalExpr(lhs->index, ctx, arena);
    uint32_t nb = key_vec.width / 8;
    std::string s;
    s.reserve(nb);
    for (uint32_t i = nb; i > 0; --i) {
      uint32_t bi = i - 1;
      auto ch = static_cast<char>(
          (key_vec.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
      if (ch != 0) s.push_back(ch);
    }
    aa->str_data[s] = rhs_val;
  } else {
    auto key_val = EvalExpr(lhs->index, ctx, arena);
    if (HasUnknownBits(key_val)) {
      ctx.GetDiag().Warning({}, "associative array index contains x/z",
                            Subclause::Unread());
      return true;
    }
    auto key = AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                           aa->is_index_signed);
    aa->int_data[key] = rhs_val;
  }
  return true;
}

bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena&) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(lhs->base->text);
  if (!q || !lhs->index) return false;
  auto& arena = ctx.GetArena();
  bool idx_xz = false;
  auto idx = EvalQueueIndex(lhs->index, q, ctx, arena, &idx_xz);

  if (idx_xz) {
    ctx.GetDiag().Warning({}, "queue write index contains x/z",
                          Subclause::Unread());
    return true;
  }
  auto sz = static_cast<int64_t>(q->elements.size());

  if (idx == sz) {
    bool has_room = (q->max_size < 0) ||
                    (static_cast<int32_t>(q->elements.size()) < q->max_size);
    if (has_room) {
      q->elements.push_back(rhs_val);
      q->element_ids.push_back(q->AllocateId());
      ++q->generation;
    } else {
      ctx.GetDiag().Warning({}, "bounded queue overflow in indexed write",
                            Subclause::Unread());
    }
    return true;
  }
  if (idx >= 0 && idx < sz) {
    q->elements[static_cast<size_t>(idx)] = rhs_val;
    return true;
  }

  ctx.GetDiag().Warning({}, "queue write index out of bounds",
                        Subclause::Unread());
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
  return static_cast<int64_t>(raw);
}

static bool CollectFromQueueSlice(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind != ExprKind::kSelect || !expr->base || !expr->index_end)
    return false;
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
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
  if (expr->base->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = EvalQueueIndex(expr->index, q, ctx, arena);
  if (idx >= 0 && static_cast<size_t>(idx) < q->elements.size())
    out.push_back(q->elements[static_cast<size_t>(idx)]);
  return true;
}

static void CollectFixedArrayElements(std::string_view name,
                                      const ArrayInfo& ai, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.lo + i;
    auto ename = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(ename);
    if (v) out.push_back(v->value);
  }
}

// Collect what one item of an unpacked array concatenation contributes.
//
// §10.10.3: "each item of an unpacked array concatenation shall have a
// self-determined type ... but a complete unpacked array concatenation has no
// self-determined type. Consequently it shall be illegal for an unpacked array
// concatenation to appear as an item in another unpacked array concatenation.
// This rule makes it possible for a vector or string concatenation to appear as
// an item in an unpacked array concatenation without ambiguity." So braces
// written inside the outer braces are not a nested array concatenation to be
// flattened -- they are a vector or string concatenation, self-determined, and
// they contribute the single value they evaluate to. The clause's own example
// assigns {S1, SQ, {"element 3 is ", S2}} and ends with "element 3 is S2" as
// one element.
//
// An item that names a queue or an unpacked array still contributes that
// object's elements; it is the brace form alone that stops being expanded.
static void CollectQueueItem(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  if (CollectFromQueueSlice(expr, ctx, arena, out)) return;
  if (CollectFromQueueElem(expr, ctx, arena, out)) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* q = ctx.FindQueue(expr->text);
    if (q) {
      out.insert(out.end(), q->elements.begin(), q->elements.end());
      return;
    }

    auto* ai = ctx.FindArrayInfo(expr->text);
    if (ai) {
      CollectFixedArrayElements(expr->text, *ai, ctx, out);
      return;
    }
  }
  if (TryCollectLocatorResult(expr, ctx, arena, out)) return;
  // §7.4.5: a slice of an unpacked array is itself an unpacked array, so it
  // contributes the elements it names rather than the one value their
  // concatenation would make.
  if (CollectUnpackedSliceElements(expr, ctx, arena, out)) return;
  out.push_back(EvalExpr(expr, ctx, arena));
}

// The outermost braces of the right-hand side are the unpacked array
// concatenation, so its items are collected one by one. A right-hand side that
// is not a concatenation at all is itself the single item.
//
// An assignment pattern is the other form whose items are the destination's
// elements. §10.10.3's example assigns one to a queue of strings,
//
//   SQ = '{"element 0", "element 1"};   // assignment pattern, two strings
//
// and says it holds two. Unlike the brace form there is no ambiguity to resolve
// here: an assignment pattern is only ever written where its items are the
// aggregate's elements, so the outer one is expanded for the same reason the
// outer braces are.
//
// Only the plain positional form is expanded. A keyed pattern carries its items
// under pattern_keys and a replicated one carries a single replication node,
// and neither is a list of elements in positional order; walking those as if
// they were would put one wrong value per key or per replication into the
// queue. They keep the single-item reading they already had rather than a
// guessed expansion.
static bool IsPositionalPattern(const Expr* expr) {
  if (expr->kind != ExprKind::kAssignmentPattern) return false;
  if (!expr->pattern_keys.empty() || expr->elements.empty()) return false;
  return expr->elements.size() != 1 ||
         expr->elements[0]->kind != ExprKind::kReplicate;
}

static void CollectQueueElements(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::vector<Logic4Vec>& out) {
  if (expr->kind == ExprKind::kConcatenation || IsPositionalPattern(expr)) {
    for (auto* elem : expr->elements) CollectQueueItem(elem, ctx, arena, out);
    return;
  }
  CollectQueueItem(expr, ctx, arena, out);
}

static void CopyNewInit(const Expr* rhs, QueueObject* q,
                        const std::vector<Logic4Vec>& saved, SimContext& ctx) {
  if (rhs->args.size() < 2) return;
  auto* init_expr = rhs->args[1];
  if (!init_expr || init_expr->kind != ExprKind::kIdentifier) return;
  auto* src = ctx.FindQueue(init_expr->text);
  if (!src) return;

  const auto& src_elems = (src == q) ? saved : src->elements;
  size_t copy_len = std::min(q->elements.size(), src_elems.size());
  for (size_t i = 0; i < copy_len; ++i) q->elements[i] = src_elems[i];
}

bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kIdentifier) return false;
  auto* q = ctx.FindQueue(stmt->lhs->text);
  if (!q) return false;
  if (stmt->rhs->kind == ExprKind::kConcatenation &&
      stmt->rhs->elements.empty()) {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    return true;
  }
  if (stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new" &&
      !stmt->rhs->args.empty()) {
    auto sz_val = EvalExpr(stmt->rhs->args[0], ctx, arena);
    int64_t sz = SignExtend(sz_val.ToUint64(), sz_val.width);

    if (sz < 0) {
      ctx.GetDiag().Error({}, "dynamic array new[] size is negative",
                          Subclause::Unread());
      return true;
    }

    auto saved = q->elements;
    q->elements.resize(static_cast<size_t>(sz),
                       MakeLogic4VecVal(arena, q->elem_width, 0));
    CopyNewInit(stmt->rhs, q, saved, ctx);
    q->AssignFreshIds();
    ++q->generation;
    return true;
  }
  std::vector<Logic4Vec> elems;
  CollectQueueElements(stmt->rhs, ctx, arena, elems);
  if (q->max_size > 0 && static_cast<int32_t>(elems.size()) > q->max_size) {
    elems.resize(static_cast<size_t>(q->max_size));
    ctx.GetDiag().Warning({}, "bounded queue overflow in assignment",
                          Subclause::Unread());
  }
  q->elements = std::move(elems);
  q->AssignFreshIds();
  ++q->generation;
  return true;
}

}  // namespace delta
