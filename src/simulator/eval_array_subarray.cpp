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
  return info.dim_sizes.size() >= 2;
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

// The subarray whose leaves are being copied, `sub`, and the context and arena
// the local copies are made in.
struct LeafBinding {
  const ArrayInfo& sub;
  SimContext& ctx;
  Arena& arena;
};

// The leaves of the subarray `lb` describes, from dimension `dim` inward: each
// leaf of the array under `src`, `src[j]...`, copied into a local variable of
// the current scope under `dst`, `dst[j]...`, with the element type's
// signedness (CollectVecElements).
static void BindSubarrayLeaves(const LeafBinding& lb, const std::string& src,
                               const std::string& dst, size_t dim) {
  const ArrayInfo& sub = lb.sub;
  bool is_multi = !sub.dim_sizes.empty();
  uint32_t lo = is_multi ? sub.dim_los[dim] : sub.lo;
  uint32_t size = is_multi ? sub.dim_sizes[dim] : sub.size;
  if (is_multi && dim + 1 < sub.dim_sizes.size()) {
    for (uint32_t j = 0; j < size; ++j) {
      std::string index = "[" + std::to_string(lo + j) + "]";
      BindSubarrayLeaves(lb, src + index, dst + index, dim + 1);
    }
    return;
  }
  ArrayInfo row;
  row.lo = lo;
  row.size = size;
  row.elem_width = sub.elem_width;
  row.is_4state = sub.is_4state;
  std::vector<Logic4Vec> leaves =
      CollectVecElements(src, row, lb.ctx, lb.arena);
  for (uint32_t j = 0; j < size; ++j) {
    auto* name =
        lb.arena.Create<std::string>(dst + "[" + std::to_string(lo + j) + "]");
    lb.ctx.CreateLocalVariable(*name, sub.elem_width, leaves[j].is_signed)
        ->value = leaves[j];
  }
}

void BindSubarrayIterator(const SubarrayElement& element,
                          std::string_view iter_name, SimContext& ctx,
                          Arena& arena) {
  ArrayInfo sub = SubarrayInfo(element.info);
  std::string src = std::string(element.array_name) + "[" +
                    std::to_string(element.info.dim_los[0] + element.offset) +
                    "]";
  BindSubarrayLeaves(LeafBinding{sub, ctx, arena}, src, std::string(iter_name),
                     0);
  ctx.RegisterArrayInScope(iter_name, sub);
}

}  // namespace delta
