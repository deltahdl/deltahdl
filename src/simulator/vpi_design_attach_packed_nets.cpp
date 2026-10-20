#include <cstddef>
#include <cstdint>
#include <string>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_nets.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// One packed array net whose subelements are being made: the net itself,
// which detail 31 makes the vpiParent of every one of them, the packed
// dimensions it declares, the kind of net past the last of them, and the
// model to build in.
struct PackedNetShape {
  VpiObject* top;
  const PackedDims& dims;
  int leaf_kind;
  const VpiAttachBuild& build;
};

// The kind of net a packed array net of `kind` holds past its last packed
// dimension: a packed struct, union or enum net (§37.16 detail 1).
int LeafKindOf(DataTypeKind kind) {
  if (kind == DataTypeKind::kStruct) return vpiStructNet;
  return kind == DataTypeKind::kUnion ? vpiUnionNet : vpiEnumNet;
}

// §37.16 detail 32: the subelements of `holder`, which stands for the packed
// dimensions of `shape` from `depth` on and sits `offset` bits above the least
// significant end of the net, one per index of the dimension at `depth`, the
// leftmost first and most significant: a packed array net while dimensions
// remain and past the last a net of the leaf kind. Each is named by its
// index, carries it for vpiIndex, and has the whole packed array net as its
// vpiParent (detail 31).
void MakeSubelements(VpiObject* holder, std::size_t depth, int64_t offset,
                     const PackedNetShape& shape) {
  if (depth == shape.dims.size()) return;
  const PackedRange& dim = shape.dims[depth];
  const int64_t kCount = dim.HighIndex() - dim.LowIndex() + 1;
  const int64_t kWidth = holder->size / kCount;
  const bool kLeaf = depth + 1 == shape.dims.size();
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  int64_t place = kCount - 1;
  for (int64_t index = dim.left;; index += kStep, --place) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    VpiObject* sub = shape.build.alloc();
    sub->type = kLeaf ? shape.leaf_kind : vpiPackedArrayNet;
    sub->parent = shape.top;
    sub->net = holder->net;
    sub->name = shape.build.keep(std::string(holder->name) + kSuffix);
    sub->full_name = holder->full_name + kSuffix;
    sub->size = static_cast<int>(kWidth);
    sub->bit_offset = static_cast<int>(offset + place * kWidth);
    sub->packed = true;
    sub->index = static_cast<int>(index);
    sub->index_expr = VpiIntConstant(index, shape.build);
    sub->children.push_back(sub->index_expr);
    holder->children.push_back(sub);
    MakeSubelements(sub, depth + 1, sub->bit_offset, shape);
    if (index == dim.right) break;
  }
}

}  // namespace

void AttachPackedArrayNetElements(const RtlirDesign* design,
                                  const VpiObjectMap& objects, SimContext& ctx,
                                  const VpiAttachBuild& build) {
  ForEachDeclaredNetObject(
      design, objects,
      [&](const RtlirNet& net, VpiObject& obj, const std::string& prefix) {
        if (VpiNetObjectKind(net) != vpiPackedArrayNet) return;
        // The dimensions are evaluated in the instance declaring the net.
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        const PackedDims kDims = WrittenPackedDims(net.dtype, ctx);
        MakeSubelements(&obj, 0, 0,
                        {&obj, kDims, LeafKindOf(net.data_kind), build});
      });
}

}  // namespace delta
