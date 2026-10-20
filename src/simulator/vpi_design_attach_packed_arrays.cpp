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

// One packed array net or var whose subelements are being made: the object
// itself, which §37.16 detail 31 and §37.18 detail 3 make the vpiParent of
// every one of them, the packed dimensions it declares, the kind of a
// subelement while dimensions remain and the kind past the last of them, and
// the model to build in.
struct PackedArrayShape {
  VpiObject* top;
  const PackedDims& dims;
  int array_kind;
  int leaf_kind;
  const VpiAttachBuild& build;
};

// The kind of net a packed array net of `kind` holds past its last packed
// dimension: a packed struct, union or enum net (§37.16 detail 1).
int LeafNetKindOf(DataTypeKind kind) {
  if (kind == DataTypeKind::kStruct) return vpiStructNet;
  return kind == DataTypeKind::kUnion ? vpiUnionNet : vpiEnumNet;
}

// The kind of variable the packed array var `var` holds past its last packed
// dimension: a struct, union or enum var (§37.18 detail 1), the struct or
// union its type resolves to where it names no enum.
int LeafVarKindOf(const RtlirVariable& var) {
  if (!var.enum_type_name.empty()) return vpiEnumVar;
  return var.dtype->kind == DataTypeKind::kUnion ? vpiUnionVar : vpiStructVar;
}

// The run's bits of the subelement `sub`, `offset` bits above the least
// significant end of the packed array. A net's subelement reads them out of
// the net's storage directly. A var's holds a copy of them kept in step with
// the variable's (VpiRefreshElementCopy), as a member does, and is a vector
// (§37.18 detail 1).
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

// §37.16 detail 32 and §37.18 detail 3: the subelements of `holder`, which
// stands for the packed dimensions of `shape` from `depth` on and sits
// `offset` bits above the least significant end of the packed array, one per
// index of the dimension at `depth`, the leftmost first and most significant:
// a packed array while dimensions remain and past the last one of the leaf
// kind. Each is named by its index, carries it for vpiIndex, and has the whole
// packed array as its vpiParent (§37.16 detail 31, §37.17 detail 26).
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
  const DataType* type = var.dtype != nullptr ? var.dtype : written;
  return type->kind == DataTypeKind::kStruct ||
         type->kind == DataTypeKind::kUnion;
}

void AttachPackedArrayElements(const RtlirDesign* design,
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
