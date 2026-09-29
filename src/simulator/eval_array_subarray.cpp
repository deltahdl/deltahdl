#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/eval_array_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

bool HasSubarrayElements(const ArrayInfo& info) {
  return info.dim_sizes.size() >= 2 &&
         info.dim_los.size() == info.dim_sizes.size();
}

// The entries of `v` after its first, which describe the dimensions of one of
// the array's elements.
template <typename T>
static std::vector<T> AfterFirst(const std::vector<T>& v) {
  auto skip = static_cast<std::ptrdiff_t>(std::min<size_t>(1, v.size()));
  return std::vector<T>(v.begin() + skip, v.end());
}

// §7.4.4: the shape of one element of the multidimensional array `info`
// describes, a subarray of every dimension but the first. A subarray of one
// dimension leaves dim_los and dim_sizes empty, as ArrayInfo describes any
// one-dimensional array.
static ArrayInfo SubarrayInfo(const ArrayInfo& info) {
  ArrayInfo sub;
  sub.lo = info.dim_los[1];
  sub.size = info.dim_sizes[1];
  sub.elem_width = info.elem_width;
  sub.is_4state = info.is_4state;
  sub.elem_type_kind = info.elem_type_kind;
  if (info.dim_sizes.size() > 2) {
    sub.dim_los = AfterFirst(info.dim_los);
    sub.dim_sizes = AfterFirst(info.dim_sizes);
    sub.dim_descending = AfterFirst(info.dim_descending);
  }
  return sub;
}

// The leaves of subarray `sub` from dimension `dim` inward: each leaf of the
// array under `src`, `src[j]...`, copied into a local variable of the current
// scope under `dst`, `dst[j]...`, with the element type's signedness
// (CollectVecElements).
static void BindSubarrayLeaves(const std::string& src, const std::string& dst,
                               const ArrayInfo& sub, size_t dim,
                               SimContext& ctx, Arena& arena) {
  bool is_multi = !sub.dim_sizes.empty();
  uint32_t lo = is_multi ? sub.dim_los[dim] : sub.lo;
  uint32_t size = is_multi ? sub.dim_sizes[dim] : sub.size;
  if (is_multi && dim + 1 < sub.dim_sizes.size()) {
    for (uint32_t j = 0; j < size; ++j) {
      std::string index = "[" + std::to_string(lo + j) + "]";
      BindSubarrayLeaves(src + index, dst + index, sub, dim + 1, ctx, arena);
    }
    return;
  }
  ArrayInfo row;
  row.lo = lo;
  row.size = size;
  row.elem_width = sub.elem_width;
  row.is_4state = sub.is_4state;
  std::vector<Logic4Vec> leaves = CollectVecElements(src, row, ctx, arena);
  for (uint32_t j = 0; j < size; ++j) {
    auto* name =
        arena.Create<std::string>(dst + "[" + std::to_string(lo + j) + "]");
    ctx.CreateLocalVariable(*name, sub.elem_width, leaves[j].is_signed)->value =
        leaves[j];
  }
}

void BindSubarrayIterator(std::string_view var_name, const ArrayInfo& info,
                          uint32_t offset, std::string_view iter_name,
                          SimContext& ctx, Arena& arena) {
  ArrayInfo sub = SubarrayInfo(info);
  std::string src = std::string(var_name) + "[" +
                    std::to_string(info.dim_los[0] + offset) + "]";
  BindSubarrayLeaves(src, std::string(iter_name), sub, 0, ctx, arena);
  ctx.RegisterArrayInScope(iter_name, sub);
}

}  // namespace delta
