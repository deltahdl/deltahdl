#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
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
// and §7.6 pairs one with another by position rather than by index --
// "Correspondence between elements is determined by the left-to-right order of
// elements in each array". §7.6 also settles the window itself, since "an
// assignment where the left-hand side contains a slice is treated as a single
// assignment to the entire slice".
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

bool TrySubarrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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
