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
#include "parser/ast_stmt.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// §7.4.6's assignments between unpacked arrays taken element by element: a
// slice of one written from a slice of another or from a packed value
// (TryUnpackedSliceAssign), and a subarray copied element by element
// (TrySubarrayAssign).

// §7.4.6: destination window of an unpacked-array slice assignment, i.e. the
// elements `base[dst_lo .. dst_lo+dst_count)` each `elem_width` bits wide.
struct UnpackedSliceTarget {
  std::string_view base;
  uint32_t dst_lo;
  uint32_t dst_count;
  uint32_t elem_width;
  // The declared direction of the array the window is cut from. `dst_lo` is the
  // numerically lowest index either way, so this is what says which end of the
  // window receives the first source element.
  bool is_descending;
};

// The index that position `i` of the destination window occupies, counting
// positions in the declared order of the array rather than by ascending index.
static uint32_t SliceTargetIndex(const UnpackedSliceTarget& dst, uint32_t i) {
  return dst.is_descending ? (dst.dst_lo + dst.dst_count - 1 - i)
                           : (dst.dst_lo + i);
}

// When no element-wise source was collected, evaluate the rhs as a single
// packed value and split it into `dst.dst_count` element-width slices.
//
// The concatenation a slice reads as puts the lowest-indexed element in the low
// bits, so the low field belongs to index `dst_lo` whichever way the array
// runs. The writer places source position i by declared order, so on a
// descending destination the low field is the last position rather than the
// first, and the fields are emitted from the top down to land where they came
// from.
static void FillSliceSourceFromPacked(const Stmt* stmt,
                                      const UnpackedSliceTarget& dst,
                                      SimContext& ctx, Arena& arena,
                                      std::vector<Logic4Vec>& src) {
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  uint32_t elem_width = dst.elem_width;
  uint64_t mask =
      (elem_width >= 64) ? ~uint64_t{0} : (uint64_t{1} << elem_width) - 1;
  for (uint32_t i = 0; i < dst.dst_count; ++i) {
    uint32_t field = dst.is_descending ? (dst.dst_count - 1 - i) : i;
    src.push_back(MakeLogic4VecVal(
        arena, elem_width, (val.ToUint64() >> (field * elem_width)) & mask));
  }
}

// Write the collected source elements into the destination slice elements
// `dst.base[dst.dst_lo .. dst.dst_lo+dst.dst_count)`, resizing/coercing as for
// a scalar write. Source position i fills the window's i'th element in the
// destination array's declared order: §7.4.5 makes both sides unpacked arrays,
// and §7.6 pairs one with another by position rather than by index, matching
// elements by their left-to-right order in each array. §7.6 also settles the
// window itself, since it treats an assignment to a slice as one assignment to
// the whole slice.
static void WriteUnpackedSliceElements(const UnpackedSliceTarget& dst,
                                       const std::vector<Logic4Vec>& src,
                                       SimContext& ctx, Arena& arena) {
  for (uint32_t i = 0; i < dst.dst_count && i < src.size(); ++i) {
    auto n = std::string(dst.base) + "[" +
             std::to_string(SliceTargetIndex(dst, i)) + "]";
    auto* var = ctx.FindVariable(n);
    if (!var) continue;
    var->value = ResizeToWidth(src[i], var->value.width, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  }
}

bool TryUnpackedSliceAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto* lhs = stmt->lhs;
  if (lhs->kind != ExprKind::kSelect || !lhs->index_end) return false;
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return false;
  auto* dst_info = ctx.FindArrayInfo(lhs->base->text);
  if (!dst_info) return false;
  auto [dst_lo, dst_count] = SelectRange(lhs, ctx, arena);
  UnpackedSliceTarget dst{lhs->base->text, dst_lo, dst_count,
                          dst_info->elem_width, dst_info->is_descending};
  std::vector<Logic4Vec> src;
  // The collector answers each element with a copy of its own, so its entries
  // are the destination's to keep; the packed fallback builds its fields fresh
  // and owns them likewise.
  if (!CollectUnpackedSliceElements(stmt->rhs, ctx, arena, src) || src.empty())
    FillSliceSourceFromPacked(stmt, dst, ctx, arena, src);
  WriteUnpackedSliceElements(dst, src, ctx, arena);
  return true;
}

static Variable* FindOrCreateElement(const std::string& name, uint32_t width,
                                     SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(name);
  if (var) return var;
  return ctx.CreateVariable(*arena.Create<std::string>(name), width);
}

static bool IsCompoundSelect(const Expr* expr) {
  return expr && expr->kind == ExprKind::kSelect && expr->base &&
         expr->base->kind == ExprKind::kSelect && !expr->index_end;
}

// §7.4.4: a fixed-size array, or the subarray a select of one names by
// omitting its fastest-varying indices -- `A[1]` of `int A[2][3]`,
// `A[0][2]` of `int A[2][3][4]` -- as the names of its elements in the
// positional order §7.6 pairs two arrays by, and the sizes of its remaining
// dimensions.
struct SubarrayElems {
  std::vector<std::string> names;
  std::vector<uint32_t> shape;
};

// One dimension of a fixed-size array as §7.6 walks it: its low bound, its
// element count, and whether it is declared from the higher bound down.
struct DeclaredDim {
  uint32_t lo;
  uint32_t size;
  bool descending;
};

// The dimensions `info` records, outermost first: a multidimensional array's
// each, a one-dimensional array's one.
static std::vector<DeclaredDim> DeclaredDims(const ArrayInfo& info) {
  std::vector<DeclaredDim> dims;
  if (info.dim_sizes.size() < 2 ||
      info.dim_los.size() != info.dim_sizes.size()) {
    dims.push_back({info.lo, info.size, info.is_descending});
    return dims;
  }
  for (size_t d = 0; d < info.dim_sizes.size(); ++d) {
    bool desc = d < info.dim_descending.size() ? info.dim_descending[d]
                                               : d == 0 && info.is_descending;
    dims.push_back({info.dim_los[d], info.dim_sizes[d], desc});
  }
  return dims;
}

// Appends the name of every element under `prefix` across `dims` from `d`
// on, each dimension walked from its left bound (§7.6 matches elements by
// their left-to-right order in each array).
static void AppendLeftToRight(const std::vector<DeclaredDim>& dims, size_t d,
                              const std::string& prefix,
                              std::vector<std::string>& out) {
  if (d == dims.size()) {
    out.push_back(prefix);
    return;
  }
  const DeclaredDim& dim = dims[d];
  for (uint32_t i = 0; i < dim.size; ++i) {
    uint32_t index = dim.descending ? dim.lo + dim.size - 1 - i : dim.lo + i;
    AppendLeftToRight(dims, d + 1, prefix + "[" + std::to_string(index) + "]",
                      out);
  }
}

// `expr` as a whole fixed-size array or one of its subarrays, into `out`;
// false for an expression naming an element, a slice or anything else.
static bool ResolveSubarray(const Expr* expr, SimContext& ctx, Arena& arena,
                            SubarrayElems& out) {
  std::vector<const Expr*> indices;
  const Expr* e = expr;
  for (; e != nullptr && e->kind == ExprKind::kSelect; e = e->base) {
    if (e->index == nullptr || e->index_end != nullptr) return false;
    indices.insert(indices.begin(), e->index);
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* info = ctx.FindArrayInfo(e->text);
  if (info == nullptr || info->is_dynamic || info->is_queue) return false;
  std::vector<DeclaredDim> dims = DeclaredDims(*info);
  if (indices.size() >= dims.size()) return false;
  std::string prefix(e->text);
  for (const Expr* index : indices) {
    prefix += "[" +
              std::to_string(static_cast<int64_t>(
                  EvalExpr(index, ctx, arena).ToUint64())) +
              "]";
  }
  dims.erase(dims.begin(), dims.begin() + static_cast<long>(indices.size()));
  for (const DeclaredDim& dim : dims) out.shape.push_back(dim.size);
  AppendLeftToRight(dims, 0, prefix, out.names);
  return true;
}

// The element values of the source of an assignment to the subarray `dst`:
// another fixed-size array or subarray of its shape, or a dynamic array or
// queue of its element count; false where the source is none of these, and
// a §7.6 error, the assignment writing nothing, where the sizes differ.
static bool SubarraySourceValues(const Stmt* stmt, const SubarrayElems& dst,
                                 SimContext& ctx, Arena& arena,
                                 std::vector<Logic4Vec>& vals) {
  SubarrayElems src;
  bool sized = false;
  if (ResolveSubarray(stmt->rhs, ctx, arena, src)) {
    sized = src.shape == dst.shape;
    for (const std::string& name : src.names) {
      const Variable* v = ctx.FindVariable(name);
      vals.push_back(v != nullptr ? OwnRhsWords(v->value, arena)
                                  : MakeLogic4VecVal(arena, 32, 0));
    }
  } else if (const QueueObject* q = stmt->rhs->kind == ExprKind::kIdentifier
                                        ? ctx.FindQueue(stmt->rhs->text)
                                        : nullptr) {
    sized = dst.shape.size() == 1 && q->elements.size() == dst.shape[0];
    for (const auto& elem : q->elements)
      vals.push_back(OwnRhsWords(elem, arena));
  } else {
    return false;
  }
  if (!sized) {
    ctx.GetDiag().Error(stmt->range.start,
                        "array size mismatch in assignment to fixed-size array",
                        Subclause("7.6"));
    vals.clear();
  }
  return true;
}

// §7.4.4 with §7.6: an assignment one of whose sides is a subarray of a
// multidimensional fixed-size array, `A[1] = B[0]`, `A[0][2] = C[0]`,
// `R = B[1]`, or a dynamic array assigned to such a subarray, copies element
// by element by position. False where neither side is a select naming a
// subarray or the other side is no array.
static bool TryFixedSubarrayAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (stmt->rhs == nullptr || (stmt->lhs->kind != ExprKind::kSelect &&
                               stmt->rhs->kind != ExprKind::kSelect)) {
    return false;
  }
  SubarrayElems dst;
  if (!ResolveSubarray(stmt->lhs, ctx, arena, dst)) return false;
  std::vector<Logic4Vec> vals;
  if (!SubarraySourceValues(stmt, dst, ctx, arena, vals)) return false;
  for (size_t i = 0; i < vals.size() && i < dst.names.size(); ++i) {
    Variable* var = ctx.FindVariable(dst.names[i]);
    if (var == nullptr) continue;
    var->value = ResizeToWidth(vals[i], var->value.width, arena);
    if (!var->is_4state) CoerceTo2State(var->value);
    var->NotifyWatchers();
  }
  return true;
}

// §10.9.1 with §7.4.4: an assignment pattern assigned to a subarray of a
// multidimensional fixed-size array, `A[1] = '{6, 4, 9}` or `M[1] =
// '{'{1, 2}, '{3, 4}}`, fills it element by element as it fills an array of
// the subarray's shape. Taken as one value written into a select, the pattern
// wrote no element.
static bool TrySubarrayPatternAssign(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (stmt->lhs->kind != ExprKind::kSelect || stmt->rhs == nullptr ||
      stmt->rhs->kind != ExprKind::kAssignmentPattern) {
    return false;
  }
  std::string prefix;
  ArrayInfo sub;
  if (!ResolveSubarraySelect(stmt->lhs, ctx, arena, prefix, sub)) return false;
  DistributePatternToArray(prefix, sub, stmt->rhs, ctx, arena);
  return true;
}

bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TrySubarrayPatternAssign(stmt, ctx, arena)) return true;
  if (TryFixedSubarrayAssign(stmt, ctx, arena)) return true;
  if (!IsCompoundSelect(stmt->lhs) || !IsCompoundSelect(stmt->rhs))
    return false;
  std::string dst_prefix, src_prefix;
  if (!BuildCompoundLhsName(stmt->lhs, ctx, arena, dst_prefix)) return false;
  if (!BuildCompoundLhsName(stmt->rhs, ctx, arena, src_prefix)) return false;
  std::string match = src_prefix + "[";
  std::vector<std::pair<std::string, Logic4Vec>> elems;
  // Each element of the source subarray is a storage element of its own under
  // §6.8, so the run is copied where it is gathered rather than shared with
  // the destination's elements. This handler runs ahead of the right-hand
  // value the statement executor makes and gathers its own, so none of that
  // value's copy reaches here; and the store below neither resizes nor
  // coerces, so `b = a` was quiet where it paired the elements up and the
  // shared words only showed on the next write to either array.
  for (const auto& [vname, vptr] : ctx.GetVariables()) {
    if (vname.starts_with(match))
      elems.emplace_back(std::string(vname.substr(src_prefix.size())),
                         OwnRhsWords(vptr->value, arena));
  }
  if (elems.empty()) return false;
  for (const auto& [suffix, val] : elems) {
    auto* dst = FindOrCreateElement(dst_prefix + suffix, val.width, ctx, arena);
    dst->value = val;
    dst->NotifyWatchers();
  }
  return true;
}

}  // namespace delta
