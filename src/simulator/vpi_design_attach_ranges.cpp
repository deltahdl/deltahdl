#include <cstddef>
#include <optional>
#include <string>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_dynamic_ranges.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// One dimension as §37.22 draws it: the bounds of a fixed one, none for a
// dynamic, queue or associative one, which is an empty range.
using DimBounds = std::optional<PackedRange>;

// §37.17 detail 4: the unpacked dimensions of `var`, leftmost first. A queue,
// dynamic or associative array's leftmost dimension is an empty range, and
// so is every dimension whose bounds did not fold.
std::vector<DimBounds> UnpackedDims(const RtlirVariable& var) {
  std::vector<DimBounds> dims;
  if (var.is_queue || var.is_dynamic || var.is_assoc) dims.emplace_back();
  for (const RtlirUnpackedDim& dim : var.unpacked_dims) {
    dims.emplace_back(PackedRange{dim.left, dim.right});
  }
  while (dims.size() < var.num_unpacked_dims) dims.emplace_back();
  return dims;
}

// The dimensions vpiRange iterates for `var`: an array var's unpacked
// dimensions, and otherwise the packed dimensions it declares (detail 4),
// which leave out the implicit range of a packed struct or union.
std::vector<DimBounds> RangeDims(const RtlirVariable& var, SimContext& ctx) {
  std::vector<DimBounds> dims = UnpackedDims(var);
  if (!dims.empty()) return dims;
  for (const PackedRange& dim : WrittenPackedDims(var.dtype, ctx)) {
    dims.emplace_back(dim);
  }
  return dims;
}

// §37.16 detail 26: the packed dimensions `net` declares, which leave out the
// implicit range of a packed struct or union net and the base type's of an
// enum net (detail 1).
std::vector<DimBounds> PackedNetDims(const RtlirNet& net, SimContext& ctx) {
  std::vector<DimBounds> dims;
  if (!net.has_declared_packed_dim) return dims;
  for (const PackedRange& dim : WrittenPackedDims(net.dtype, ctx)) {
    dims.emplace_back(dim);
  }
  return dims;
}

// Detail 4: a range object per dimension under `obj`, leftmost first. Detail
// 6: the leftmost one's bounds are the variable's vpiLeftRange and
// vpiRightRange, which are null where that range is empty. Answers the
// leftmost range, null where there are none.
VpiObject* AttachRanges(VpiObject* obj, const std::vector<DimBounds>& dims,
                        const VpiAttachBuild& build) {
  if (dims.empty()) return nullptr;
  VpiObject* leftmost = VpiRangeObject(obj, dims.front(), build);
  obj->children.push_back(leftmost);
  for (std::size_t i = 1; i < dims.size(); ++i) {
    obj->children.push_back(VpiRangeObject(obj, dims[i], build));
  }
  obj->left_range = leftmost->left_range;
  obj->right_range = leftmost->right_range;
  return leftmost;
}

// §37.16 detail 26: the ranges vpiRange reaches from `net`, keyed under
// `prefix`: an array net's unpacked ranges, and a net's packed ones, a net in
// an array net's among them, which the run keys under its element's name.
void AttachNetRanges(const RtlirNet& net, const std::string& prefix,
                     const VpiObjectMap& objects, SimContext& ctx,
                     const VpiAttachBuild& build) {
  const std::vector<DimBounds> kPacked = PackedNetDims(net, ctx);
  for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
    VpiObject* obj = FindObjectForFlatName(objects, key);
    if (obj != nullptr) AttachRanges(obj, kPacked, build);
  }
  if (net.unpacked_dims.empty()) return;
  std::vector<DimBounds> unpacked;
  unpacked.reserve(net.unpacked_dims.size());
  for (const RtlirUnpackedDim& dim : net.unpacked_dims) {
    unpacked.emplace_back(PackedRange{dim.left, dim.right});
  }
  VpiObject* array =
      FindObjectForFlatName(objects, VpiFlatName(prefix, net.name));
  if (array != nullptr) AttachRanges(array, unpacked, build);
}

}  // namespace

VpiObject* VpiRangeObject(VpiObject* parent,
                          const std::optional<PackedRange>& bounds,
                          const VpiAttachBuild& build) {
  // §37.22: the bounds reached through vpiLeftRange and vpiRightRange and the
  // size the number of elements the dimension holds; an empty range has
  // neither bound and size 0.
  VpiObject* range = build.alloc();
  range->type = vpiRange;
  range->parent = parent;
  if (bounds) {
    range->left_range = VpiIntConstant(bounds->left, build);
    range->right_range = VpiIntConstant(bounds->right, build);
    range->size =
        static_cast<int>(bounds->HighIndex() - bounds->LowIndex() + 1);
  }
  return range;
}

void AttachDeclaredRanges(VpiObject* obj, const DataType& type,
                          const std::vector<Expr*>& unpacked_dims,
                          SimContext& ctx, const VpiAttachBuild& build) {
  std::vector<DimBounds> dims;
  dims.reserve(unpacked_dims.size());
  for (const Expr* dim : unpacked_dims) {
    dims.push_back(WrittenUnpackedDim(dim, ctx));
  }
  if (dims.empty()) {
    for (const PackedRange& dim : WrittenPackedDims(&type, ctx)) {
      dims.emplace_back(dim);
    }
  }
  AttachRanges(obj, dims, build);
}

void AttachVariableAndNetRanges(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build) {
  // §37.17 details 4 and 6 and §37.16 detail 26: a variable's and a net's
  // dimensions are reached as range objects and its leftmost bounds through
  // vpiLeftRange and vpiRightRange. A generic interconnect is shaped apart
  // with its own (AttachInterconnects).
  WalkInstancePaths(
      &design, [&](const RtlirModule* mod, const std::string& prefix) {
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        for (const RtlirVariable& var : mod->variables) {
          VpiObject* obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr) continue;
          VpiObject* leftmost = AttachRanges(obj, RangeDims(var, ctx), build);
          // §37.22 detail 1: a dynamic array's or queue's leftmost range takes
          // its bounds from the elements the array holds when it is read.
          if (var.is_queue || var.is_dynamic) {
            VpiGiveDynamicRangeBounds(*leftmost, build);
          }
        }
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          if (!VpiNetIsInterconnect(net)) {
            AttachNetRanges(net, prefix, objects, ctx, build);
          }
        }
      });
}

}  // namespace delta
