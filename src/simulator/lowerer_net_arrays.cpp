#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

// One net array whose element nets are being made: its declaration, and the
// time scale, run and arena to make them in.
struct NetArraySite {
  const RtlirNet& net;
  const TimeScale& scale;
  SimContext& ctx;
  Arena& arena;
};

// The element nets beneath dimension `depth` of the array, or of the subarray
// of it, named `prefix`: one net per address of the last dimension, and a
// subarray per address of every other, named after it, `n[1][5]`.
void CreateNetArrayLeaves(const std::string& prefix, std::size_t depth,
                          const NetArraySite& site) {
  const RtlirUnpackedDim& dim = site.net.unpacked_dims[depth];
  const bool kLast = depth + 1 == site.net.unpacked_dims.size();
  for (int64_t index = dim.Low(); index < dim.Low() + dim.Size(); ++index) {
    auto* key = site.arena.Create<std::string>(prefix + "[" +
                                               std::to_string(index) + "]");
    if (kLast) {
      CreateNetStorage(*key, site.net, site.scale, site.ctx, site.arena);
    } else {
      CreateNetArrayLeaves(*key, depth + 1, site);
    }
  }
}

}  // namespace

void CreateNetArrayElements(std::string_view name, const RtlirNet& net,
                            const TimeScale& scale, SimContext& ctx,
                            Arena& arena) {
  if (net.unpacked_dims.empty()) return;
  if (std::ranges::any_of(net.unpacked_dims, [](const RtlirUnpackedDim& dim) {
        return dim.Low() < 0;
      })) {
    return;
  }
  const RtlirUnpackedDim& outer = net.unpacked_dims.front();
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(outer.Low());
  info.size = outer.Size();
  info.elem_width = net.width;
  info.is_descending = outer.left > outer.right;
  // §7.4.5: every dimension of a multidimensional array, outermost first, as
  // a multidimensional array var records them (TryCreateMultiDimArray).
  if (net.unpacked_dims.size() > 1) {
    for (const RtlirUnpackedDim& dim : net.unpacked_dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
      info.dim_sizes.push_back(dim.Size());
      info.dim_descending.push_back(dim.left > dim.right);
    }
  }
  ctx.RegisterArray(name, info);
  CreateNetArrayLeaves(std::string(name), 0, {net, scale, ctx, arena});
}

}  // namespace delta
