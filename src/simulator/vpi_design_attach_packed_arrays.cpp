#include "simulator/vpi_design_attach_packed_arrays.h"

#include <cstddef>
#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_nets.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

struct PackedArrayShape {
  VpiObject* top;
  const PackedDims& dims;
  int array_kind;
  int leaf_kind;
  const VpiAttachBuild& build;
};

int LeafNetKindOf(DataTypeKind kind) {
  if (kind == DataTypeKind::kStruct) return vpiStructNet;
  return kind == DataTypeKind::kUnion ? vpiUnionNet : vpiEnumNet;
}

int LeafVarKindOf(const RtlirVariable& var) {
  if (!var.enum_type_name.empty()) return vpiEnumVar;
  return var.dtype->kind == DataTypeKind::kUnion ? vpiUnionVar : vpiStructVar;
}

void GiveSubelementBits(VpiObject& sub, const VpiObject& holder, int64_t offset,
                        const PackedArrayShape& shape) {
  if (shape.array_kind == vpiPackedArrayNet) {
    sub.net = holder.net;
    sub.bit_offset = static_cast<int>(offset);
    return;
  }
  auto* storage = shape.build.arena.Create<Variable>();
  storage->value = MakeLogic4Vec(shape.build.arena, sub.size);
  sub.var = storage;
  sub.member_of = shape.top;
  sub.member_offset = static_cast<uint32_t>(offset);
  sub.decl_vector = true;
}

void MakeSubelements(VpiObject* holder, std::size_t depth, int64_t offset,
                     const PackedArrayShape& shape) {
  if (depth == shape.dims.size()) return;
  const PackedRange& dim = shape.dims[depth];
  const int64_t kCount = dim.HighIndex() - dim.LowIndex() + 1;
  const int64_t kWidth = holder->size / kCount;
  const bool kLeaf = depth + 1 == shape.dims.size();
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  int64_t place = kCount - 1;
  for (int64_t index = dim.left;; index += kStep, --place) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    const int64_t kOffset = offset + place * kWidth;
    VpiObject* sub = shape.build.alloc();
    sub->type = kLeaf ? shape.leaf_kind : shape.array_kind;
    sub->parent = shape.top;
    sub->name = shape.build.keep(std::string(holder->name) + kSuffix);
    sub->full_name = holder->full_name + kSuffix;
    sub->size = static_cast<int>(kWidth);
    GiveSubelementBits(*sub, *holder, kOffset, shape);
    sub->packed = true;
    sub->index = static_cast<int>(index);
    sub->index_expr = VpiIntConstant(index, shape.build);
    sub->children.push_back(sub->index_expr);
    holder->children.push_back(sub);
    MakeSubelements(sub, depth + 1, kOffset, shape);
    if (index == dim.right) break;
  }
}

}  // namespace

bool VpiVariableIsPackedArray(const RtlirVariable& var) {
  const DataType* written = var.written_type;
  if (written == nullptr || written->kind == DataTypeKind::kEnum ||
      written->packed_dim_left == nullptr) {
    return false;
  }
  if (!var.enum_type_name.empty()) return true;
  return var.dtype->kind == DataTypeKind::kStruct ||
         var.dtype->kind == DataTypeKind::kUnion;
}

void AttachPackedArrayElements(const RtlirDesign* design,
                               const VpiObjectMap& objects, SimContext& ctx,
                               const VpiAttachBuild& build) {
  ForEachDeclaredNetObject(
      design, objects,
      [&](const RtlirNet& net, VpiObject& obj, const std::string& prefix) {
        if (VpiNetObjectKind(net) != vpiPackedArrayNet) return;
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        const PackedDims kDims = WrittenPackedDims(net.dtype, ctx);
        MakeSubelements(&obj, 0, 0,
                        {&obj, kDims, vpiPackedArrayNet,
                         LeafNetKindOf(net.data_kind), build});
      });
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          VpiObject* obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr || obj->type != vpiPackedArrayVar) continue;
          const PackedDims kDims = WrittenPackedDims(var.written_type, ctx);
          MakeSubelements(
              obj, 0, 0,
              {obj, kDims, vpiPackedArrayVar, LeafVarKindOf(var), build});
        }
      });
}

}  // namespace delta
