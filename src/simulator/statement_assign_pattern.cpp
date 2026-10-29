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

// Defined below; forward-declared so the queue-write helpers above its
// definition can call it. The default argument lives on the definition.
static int64_t EvalQueueIndex(const Expr* expr, QueueObject* q, SimContext& ctx,
                              Arena& arena, bool* has_xz);

uint32_t PatternKeyIndex(const Expr* key, SimContext& ctx, Arena& arena) {
  return static_cast<uint32_t>(EvalExpr(key, ctx, arena).ToUint64());
}

// One element slot of the unpacked-array target of an assignment pattern
// (IEEE 1800 §7.6 / §10.9.2). `idx` is the array index being filled; `info`
// is the target's ArrayInfo, whose element type selects the type-keyed
// pattern members and whose width and state the Table 6-7 fallback takes.
namespace {
struct PatternArrayElem {
  uint32_t idx;
  const ArrayInfo& info;
  // The layout of a structure element, which a default is applied to member
  // by member (EvalDefaultForElement); null for any other element.
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
  // §10.9.1: a structure element no type key matches has the pattern's type
  // keys and default applied to its members by §10.9.2's rules.
  if (slot.layout != nullptr && PatternHasTypeKey(rhs, ctx))
    return EvalStructPatternValue(rhs, slot.layout, ctx, arena);
  if (const Expr* fallback = DefaultKeyedItem(rhs))
    return EvalDefaultForElement(fallback, slot.layout, ctx, arena);
  // §10.9.1 forbids an element no rule covers, requiring one of its rules to
  // cover every element, so this is a pattern the elaborator
  // reports, and what the branch answers is §6.8's Table 6-7 default for the
  // element's own type, as the positional and multidimensional makers answer
  // it. The known zero it gave had one spelling of an illegal pattern reading
  // 00 where another read 'x.
  return slot.info.is_4state ? MakeAllX(arena, slot.info.elem_width)
                             : MakeLogic4VecVal(arena, slot.info.elem_width, 0);
}

namespace {
// §7.4.2: bundle for distributing a (possibly nested) assignment pattern into a
// fixed multidimensional unpacked array, keeping the recursive walk within the
// parameter-count limit. `layout` packs a leaf's structure pattern (§10.9.2),
// null where the elements are no structures.
struct PatternDist {
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
  const StructTypeInfo* layout;
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
    if (pat->elements.size() == 1 && pat->elements[0]->is_pattern_replication) {
      const auto& body = pat->elements[0]->elements;
      return body.empty() ? nullptr : body[pos % body.size()];
    }
    return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
  }
  // §10.9.1 resolves a keyed pattern by index, then by type, then by default.
  if (const Expr* item = IndexKeyedItem(pat, idx, pd.ctx, pd.arena))
    return item;
  if (const Expr* item =
          TypeKeyedItem(pat, SubjectOfElement(pd.info, pd.ctx), pd.ctx))
    return item;
  return DefaultKeyedItem(pat);
}

// Writes one leaf element, resized or defaulted to the element width; a
// structure pattern is packed by the element's layout, as PatternItemAt does.
static void WriteLeaf(const PatternDist& pd, const std::string& name,
                      const Expr* sub) {
  auto* elem = pd.ctx.FindVariable(name);
  if (!elem) return;
  Logic4Vec val = sub ? EvalItemForLayout(sub, pd.layout, pd.ctx, pd.arena)
                      : MakeLogic4VecVal(pd.arena, pd.info.elem_width, 0);
  // The leaf takes its own words for the reason DistributePatternToArray's
  // single-dimension store gives (§6.8/§10.9.1), and the same resize is what
  // it leans on: a leaf whose pattern item is a bare name of the leaf's own
  // width is handed that variable's Logic4Vec, and ResizeToWidth hands it
  // straight back.
  elem->value =
      OwnRhsWords(ResizeToWidth(val, pd.info.elem_width, pd.arena), pd.arena);
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

static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat);

// §10.9.1: gives the subarray at `prefix`, from dimension `d` in, the item
// `sub` standing for it. Braces are the subarray's own pattern or
// concatenation, and so is a pattern typed as an unpacked array; an unpacked
// array is copied in element for element; any other value, or no item at all,
// reaches every leaf beneath.
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

// §7.4.2/§10.9.1: distribute the assignment pattern `pat` across dimension `d`
// of the subtree rooted at `prefix`, each item of a dimension that is not the
// last going to the subarray it stands for.
static void DistributeDimPattern(const PatternDist& pd,
                                 const std::string& prefix, size_t d,
                                 const Expr* pat) {
  uint32_t lo = pd.info.dim_los[d];
  uint32_t size = pd.info.dim_sizes[d];
  bool last = (d + 1 == pd.info.dim_sizes.size());
  // §11.5.2 addresses this dimension from its smaller bound and §10.9.1 counts
  // the pattern's positional items from its left bound, which are the same
  // bound only when the dimension ascends. `i` is therefore the address offset
  // alone, and a descending dimension takes its position the other way round,
  // as the declaration path (CreateMultiDimLeaves in lowerer_var_multidim.cpp)
  // does.
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
  // §10.9.2 with §7.4: the items for an array of structures are each packed by
  // the element's layout.
  const ArrayPatternTarget kTarget{info, StructLayoutOfName(arr_name, ctx)};
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx =
        info.is_descending ? (info.lo + info.size - 1 - i) : (info.lo + i);
    auto name = std::string(arr_name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    Logic4Vec val = PatternItemAt(rhs, kTarget, i, ctx, arena);
    // §10.9.1 gives the element the value of its pattern item, and §6.8 makes
    // the element a data object that keeps its value from one assignment to the
    // next -- its own value, not a handle on the item's storage. EvalExpr
    // answers a bare item name with that variable's own Logic4Vec and a
    // Logic4Vec copies its `words` pointer, so the whole of what separates the
    // two here is the resize allocating -- and ResizeToWidth returns its
    // argument untouched when the widths already match, which is precisely the
    // item as wide as the element it fills. That is why the copy goes outside
    // the resize rather than inside it: inside, it would miss the only case
    // that aliases. `arr = '{p, 8'h00}` left arr[0] and the 8-bit `p` one
    // storage element, and the next writer that deposits in place -- a
    // packed-member assignment such as `p.hi = 4'h0` -- wrote through both.
    // Redundant on the arms where the resize or the maker allocated anyway.
    elem->value =
        OwnRhsWords(ResizeToWidth(val, info.elem_width, arena), arena);
    elem->NotifyWatchers();
  }
}

// §10.10: an element of an unpacked array concatenation may itself be an
// assignment pattern that contributes its elements (not a single value),
// either bare ('{...}) or typed (AI3'{5, 6, 7}). The typed form parses as a
// cast wrapping the pattern, and only one whose type is an unpacked array
// contributes elements; a typed structure pattern, P'{8'h1, 8'h2}, is one
// value, as the queue path already reads it.
static const Expr* AsArrayConcatPattern(const Expr* item, SimContext& ctx) {
  if (item->kind == ExprKind::kAssignmentPattern) return item;
  return UnpackedArrayTypedPattern(item, ctx);
}

// Replace each collected element with a copy that owns its words, the blocking
// mirror of SampleConcatElements (statement_assign_nonblocking.cpp). Every
// collector below pushes a variable's own vec or a queue's own elements, so
// every entry arrives aliasing live storage, and neither blocking store copies
// it: DistributeConcatToArray stores through ResizeToWidth, which returns its
// argument untouched when the widths already match, and TryQueueBlockingAssign
// moves the run straight into q->elements.
//
// §6.8 makes each destination a data object that keeps its value from one
// assignment to the next, so `b = {a}` on same-width arrays must not leave b[0]
// and a[0] as one buffer. The queue has the stronger rule: §7.10.3 has an
// assignment to a whole queue leave every reference to an element of the
// original queue outdated, and §7.10.4 says the same of these very assignments.
// Splicing q->elements in by pointer is what makes an outdated reference behave
// as a live one -- after `q = {q, 6}` a write through the old element would
// reach the new queue.
//
// Copying here rather than inside each collector reaches both entry points at
// the one place the run is produced, and asks no collector for an arena.
static void OwnConcatElements(std::vector<Logic4Vec>& elems, Arena& arena) {
  for (auto& elem : elems) elem = OwnRhsWords(elem, arena);
}

// §10.10: the values an array item contributes, read in the order its
// elements are written, through every dimension. An item of a
// multidimensional target's element type, a row, gives that row's values, so
// the target reads one element of its own per row it is given.
static void CollectArrayLeaves(std::string_view name, const ArrayInfo& ai,
                               SimContext& ctx, std::vector<Logic4Vec>& out) {
  for (uint32_t k = 0; k < ArrayElementCount(ai); ++k) {
    auto* v = ctx.FindVariable(std::string(name) + ArrayElementSuffixAt(ai, k));
    if (v) out.push_back(v->value);
  }
}

// The elements an item naming a fixed-size array or a queue contributes,
// appended to `out`; false for an item naming neither.
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
    // §10.10: a slice of an unpacked array is an array item, contributing its
    // elements in order as the queue path's collector already reads it.
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
  // A multidimensional target is held as its innermost elements, and the
  // values arrive in that order, so they are counted and stored by them.
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
      // The queue entry keeps its own words for the same §6.8 reason the
      // array-to-array arm of this copy does, in CopyArrayElements: the entry
      // and the element it is copied into are two storage elements, and the
      // queue outlives the statement that read it.
      dv->value = OwnRhsWords(src_q.elements[i], ctx.GetArena());
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

// §7.4.5: copies a slice of an unpacked array into an array, as in the clause's
// own `busB = busA[7:6];` -- the slice names two elements and the destination
// holds them as two elements, rather than as the one value their concatenation
// would make. §7.6 pairs the two by position, matching elements by their
// left-to-right order in each array, so the slice arrives in the source array's
// declared order and is written in the destination's, leaving `busB[1]` holding
// `busA[7]` whichever way each of the two was declared.
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

// §10.7: the value an associative element is written takes the element's
// width. A declared array's element is a variable the right-hand side was
// already sized against as its context (EvalRhsWithStructContext); a class
// property's is not, the property resolving to no variable, so the value
// arrives at its own width and is sized here. A string or a real is not a
// vector to resize (§6.16, §6.12).
static Logic4Vec SizedAssocElementValue(const Expr* base,
                                        const AssocArrayObject* aa,
                                        const Logic4Vec& rhs_val,
                                        SimContext& ctx, Arena& arena) {
  const bool kDeclared = base->kind == ExprKind::kIdentifier &&
                         ctx.FindAssocArray(base->text) == aa;
  if (kDeclared || rhs_val.is_string || rhs_val.is_real) return rhs_val;
  return ResizeToWidth(rhs_val, aa->elem_width, arena);
}

// §9.4.2: the element that changed is an aggregate element, which the clause
// names among the changes that have the event expression evaluated again, and
// it lives outside the variable registered under the
// array's name -- the one an `@(aa[3])` and an `always_comb` reading `aa[3]`
// both arm on. One statement wrote one entry, so it is announced once. An
// element of an object's property is a change to an object's data members,
// which the same clause names, and the watchers that can see it sit on the
// variables designating the object, which the handle finds.
static void AnnounceAssocElementWrite(const Expr* base, ClassObject* owner,
                                      SimContext& ctx) {
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
  } else if (base->kind == ExprKind::kIdentifier) {
    NotifyOwningVar(ctx, base->text);
  }
}

// §7.8: assigning to an associative array element that does not exist yet
// allocates an entry for it, and the array the target names is a declared one
// under its bare name or, since §8.5 puts no restriction on a property's type,
// a property of an object: the running method's own by its bare name (§8.11),
// or any object's through a handle, `o.count[k] = v`. FindAssocArrayOfBase
// reads both, and the class property is what the resolution answers where
// FindAssocArray knows no array of the name -- which is where such a write went
// before: every writer of TrySelectBlockingAssign declined it and the value
// went nowhere, so UVM's severity counts, `m_severity_count[s] = 0` in a method
// of uvm_report_server, left the array at size 0.
//
// §7.8 with §7.4: where the array is an element of an associative array whose
// elements are associative arrays, `m["a"][1] = 41`, the write is a write of
// that element too, and allocates it as well (ElementAssocOfSelect).
bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena) {
  if (!lhs->base || !lhs->index) return false;
  ClassObject* owner = nullptr;
  auto* aa = ElementAssocOfSelect(lhs->base, ctx, arena, /*allocate=*/true);
  if (aa == nullptr) aa = FindAssocArrayOfBase(lhs->base, ctx, arena, &owner);
  if (!aa) return false;
  Logic4Vec stored = SizedAssocElementValue(lhs->base, aa, rhs_val, ctx, arena);
  if (aa->is_string_key) {
    auto key = AssocStringKey(EvalExpr(lhs->index, ctx, arena));
    // §10.6.1 has an assign override every procedural assignment to a variable
    // and §10.6.2 says the same of a force, and §6.4 makes this
    // element a variable of its own. A statement standing on it therefore
    // ignores this write exactly as Variable::is_forced makes every other
    // writer ignore one, and an ignored write changed nothing to announce.
    auto driven = aa->str_drives.find(key);
    if (driven != aa->str_drives.end() && driven->second.Drives()) return true;
    aa->str_data[key] = stored;
  } else {
    auto key_val = EvalExpr(lhs->index, ctx, arena);
    if (HasUnknownBits(key_val)) {
      // §7.8.6: an index carrying an x or z bit is invalid and the write is a
      // no-op, so nothing changed and nothing is announced.
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

// §7.10.1: `q[i] = v` writes an element of a declared queue or, §8.5 putting
// no restriction on a property's type, of a queue property of an object --
// the running method's own by its bare name (§8.11) or any object's through a
// handle, `b.q[0] = v` -- which FindWrittenQueueOfBase resolves, `owner`
// naming the object whose watchers §9.4.2 has the write tell.
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

  // §9.4.2 has an implicit event detected on any change in the value of the
  // expression, and names both changes the two stores below make -- an
  // aggregate element and the size of a dynamically sized array. Neither is
  // visible in the queue variable's own `value`, so each store tells the
  // watchers armed on the name, which is what every mutating queue method does
  // and what §7.10.1 requires of this spelling too, a queue supporting every
  // operation a fixed-size unpacked array does, and
  // the fixed-array element write notifies through WriteVar. The append
  // notifies once for the element and the size together, a watcher
  // re-evaluating its expression rather than reading a delta.
  if (idx == sz) {
    q->elements.push_back(SizedForQueueElement(*q, rhs_val, arena));
    q->element_ids.push_back(q->AllocateId());
    ++q->generation;
    EnforceQueueBound(q, "indexed write", lhs->range.start, ctx);
    AnnounceQueueChange(lhs->base, owner, ctx);
    return true;
  }
  if (idx >= 0 && idx < sz) {
    // §10.6.1's assign and §10.6.2's force both override every procedural
    // assignment to what they stand on, and §6.4 makes this element a
    // variable of its own, so a write to a driven element is ignored and there
    // is nothing to announce.
    if (q->ElementIsDriven(static_cast<size_t>(idx))) return true;
    q->elements[static_cast<size_t>(idx)] =
        SizedForQueueElement(*q, rhs_val, arena);
    AnnounceQueueChange(lhs->base, owner, ctx);
    return true;
  }

  // §7.10.1 has a write at an invalid index ignored, so
  // the branch below and the x/z one above store nothing and owe no
  // notification: an event on a write that did not happen is a spurious one.

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
  // §7.10.1: an invalid index -- a 4-state expression holding an x or z bit,
  // or a value outside 0...$ -- makes the read return what Table 7-1 (§7.4.5)
  // lists for a nonexistent entry of the queue's element type, so such an index
  // yields a value rather than nothing. §10.10 makes the item contribute one
  // element to the concatenation whatever its index turned out to be, so every
  // path here pushes exactly one element.
  bool idx_xz = false;
  auto idx = EvalQueueIndex(expr->index, q, ctx, arena, &idx_xz);
  if (idx_xz || idx < 0 || static_cast<size_t>(idx) >= q->elements.size())
    out.push_back(NonexistentQueueElement(q, arena));
  else
    out.push_back(q->elements[static_cast<size_t>(idx)]);
  return true;
}

// §10.10: an item of an unpacked array concatenation that is itself an unpacked
// array stands for all of that item's elements, in the left-to-right order they
// have in the item. Left to right is the order the declaration writes, so an
// array declared `int a[3:0]` contributes a[3] first and a[0] last, and one
// declared `int a[0:3]` contributes them the other way round.
void CollectFixedArrayElements(std::string_view name, const ArrayInfo& ai,
                               SimContext& ctx, std::vector<Logic4Vec>& out) {
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.is_descending ? (ai.lo + ai.size - 1 - i) : (ai.lo + i);
    auto ename = std::string(name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(ename);
    if (v) out.push_back(v->value);
  }
}

// Collect what one item of an unpacked array concatenation contributes.
//
// §10.10.3: every item of an unpacked array concatenation has a self-determined
// type, but the concatenation as a whole has none, so one unpacked array
// concatenation may not be an item of another -- which is what lets a vector
// or string concatenation stand as an item without ambiguity. So braces
// written inside the outer braces are not a nested array concatenation to be
// flattened -- they are a vector or string concatenation, self-determined, and
// they contribute the single value they evaluate to. The clause's own example
// assigns {S1, SQ, {"element 3 is ", S2}} and ends with "element 3 is S2" as
// one element.
//
// An item that names a queue or an unpacked array still contributes that
// object's elements, and so does an assignment pattern typed as one,
// `T_SQ'{"p", "q"}`; it is the brace form alone that stops being expanded.
// The queue is a declared one by its bare name or a property of an object
// (§8.5), bare in a method or through a handle, so `q = {q, x}` in a method
// of the class declaring `q` appends to the property.
//
// §7.4 with §7.10: an element of an array whose elements are queues, UVM's
// `all[iter]` in `q = {q, all[iter]}` over `rsrc_sv_q_t all[int]`, is such a
// queue, and contributes its elements (ElementQueueOfSelect); read as the
// element's placeholder, it contributed one value that was no handle.
static void CollectQueueItem(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  if (CollectFromQueueSlice(expr, ctx, arena, out)) return;
  if (const QueueObject* element =
          ElementQueueOfSelect(expr, ctx, arena, /*allocate=*/false)) {
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

// §7.5.1: the optional initialization expression gives the dynamic array its
// initial contents. Each entry it initializes is a store of its own, so each
// takes a copy of the source entry's words rather than the pointer to them a
// plain Logic4Vec assignment would leave the two sharing. The clause is
// explicit about what the sharing would break: reinitializing with new
// destroys the old contents and leaves every earlier reference to an element
// outdated, and an entry still pointing at the source's words is exactly such
// a reference left live. `saved` carries the same hazard on the self-
// initializing form `d = new[n](d)`, since it is a vector copy whose entries
// are themselves pointer copies of what the array held before the resize.
static void CopyNewInit(const Expr* rhs, QueueObject* q,
                        const std::vector<Logic4Vec>& saved, SimContext& ctx,
                        Arena& arena) {
  if (rhs->args.size() < 2) return;
  auto* init_expr = rhs->args[1];
  if (!init_expr) return;
  // The initializer may be any unpacked array of the element type, a fixed
  // one, `new[3](isrc)` with `int isrc[3]`, as well as a dynamic array or a
  // queue; the array being sized is read as it stood before (`saved`).
  std::vector<Logic4Vec> collected;
  const bool kSelf = init_expr->kind == ExprKind::kIdentifier &&
                     ctx.FindQueue(init_expr->text) == q;
  if (!kSelf) CollectQueueElements(init_expr, ctx, arena, collected);
  const auto& src_elems = kSelf ? saved : collected;
  size_t copy_len = std::min(q->elements.size(), src_elems.size());
  for (size_t i = 0; i < copy_len; ++i)
    q->elements[i] = OwnRhsWords(src_elems[i], arena);
}

// §7.10/§10.10: the target is a declared queue by its bare name or, §8.5
// putting no restriction on a property's type, a queue property of an object
// -- the running method's own by its bare name (§8.11), or any object's
// through a handle, `b.q = {1, 2}` -- which FindQueueOfBase resolves.
// §9.4.3 (printed page 236) has a wait on the queue's size() block until the
// condition becomes true, and §9.4.2 names a change to an object's data
// members among what wakes a waiter, so each arm announces the change
// through AnnounceQueueChange: a property's to the object's watchers, a
// declared queue's or dynamic array's to the watchers on its name, as every
// mutating method does. Announced for a property alone, and not at all by
// the new[] arm, `q = {}`, `q = {7}` and `d = new[3]` on a declared queue or
// array left `wait (d.size() == 3)` parked for ever.
//
// §7.4 with §7.10 (printed pages 153 and 169): the target may also be one
// element of an array whose elements are queues, `fx[0]`, `aa["k"]` or
// `qq[0]`, which is itself a queue (ElementQueueOfSelect). The assignment
// writes the element, so a missing associative entry is allocated (§7.8.7),
// and the change is announced for the select as a method changing the
// element's queue announces it.
static QueueObject* QueueOfAssignTarget(const Expr* lhs, SimContext& ctx,
                                        Arena& arena, ClassObject** owner) {
  if (lhs->kind == ExprKind::kSelect) {
    return ElementQueueOfSelect(lhs, ctx, arena, /*allocate=*/true);
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
    // §7.5.1: with no initialization expression each element starts at its
    // type's default value -- each element initialized, so
    // each is a storage element of its own under §6.8 and needs its own words.
    // resize(n, value) copy-constructs every element it adds from the one
    // value it is handed, and a Logic4Vec copy copies the `words` pointer, so
    // filling that way would leave `d = new[4]` holding one buffer read four
    // times. Making one element at a time gives each its own allocation.
    // The default is Table 6-7's: x for a 4-state element, 0 for a 2-state
    // one. The array is a new one, so no element keeps what the array held
    // before; the initialization expression is what carries values over.
    // A handle's default is null, and a string's, which has no width, "".
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
  // §7.4: the fill keys each element's queue by the identity it gives it.
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
