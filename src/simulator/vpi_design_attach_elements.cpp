#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_interconnects.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct ArrayLevel {
  VpiObject* holder;
  std::string key;
  std::vector<int64_t> indices;
};

struct ArrayAttach {
  const std::vector<RtlirUnpackedDim>& dims;
  const VpiObject& array;
  const VpiObjectMap& objects;
  const VpiAttachBuild& build;
  int element_type = 0;
};

std::vector<int64_t> IndicesOf(const RtlirUnpackedDim& dim) {
  std::vector<int64_t> indices;
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  for (int64_t i = dim.left;; i += kStep) {
    indices.push_back(i);
    if (i == dim.right) break;
  }
  return indices;
}

void Adopt(VpiObject* member, const ArrayLevel& level, int64_t index,
           const VpiAttachBuild& build) {
  if (member->parent != nullptr) std::erase(member->parent->children, member);
  member->parent = level.holder;
  member->array_member = true;
  member->index = static_cast<int>(index);
  member->index_expr = VpiIntConstant(index, build);
  member->children.push_back(member->index_expr);
  for (std::size_t k = level.indices.size(); k-- > 0;) {
    member->children.push_back(VpiIntConstant(level.indices[k], build));
  }
  level.holder->children.push_back(member);
}

void AttachLevel(const ArrayLevel& level, std::size_t depth,
                 const ArrayAttach& attach) {
  const bool kInnermost = depth + 1 == attach.dims.size();
  for (int64_t index : IndicesOf(attach.dims[depth])) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    const std::string kKey = level.key + kSuffix;
    if (kInnermost) {
      VpiObject* element = FindObjectForFlatName(attach.objects, kKey);
      if (element == nullptr) continue;
      Adopt(element, level, index, attach.build);
      if (attach.element_type != 0) element->type = attach.element_type;
      element->decl_scalar = attach.array.decl_scalar;
      element->decl_vector = attach.array.decl_vector;
      continue;
    }
    VpiObject* subarray = attach.build.alloc();
    subarray->type = attach.array.type;
    subarray->array_type = attach.array.array_type;
    subarray->name =
        attach.build.keep(std::string(level.holder->name) + kSuffix);
    subarray->full_name = level.holder->full_name + kSuffix;
    subarray->size = static_cast<int>(attach.dims[depth + 1].Size());
    Adopt(subarray, level, index, attach.build);
    ArrayLevel inner{subarray, kKey, level.indices};
    inner.indices.push_back(index);
    AttachLevel(inner, depth + 1, attach);
  }
}

void RecordDimensionIndices(VpiObject& array,
                            const std::vector<RtlirUnpackedDim>& dims) {
  array.array_dim_indices.clear();
  for (const RtlirUnpackedDim& dim : dims) {
    std::vector<int>& indices = array.array_dim_indices.emplace_back();
    for (int64_t index : IndicesOf(dim)) {
      indices.push_back(static_cast<int>(index));
    }
  }
}

int DeclaredElementType(const RtlirVariable& var) {
  if (!var.class_type_name.empty()) return vpiClassVar;
  const int kKind = VpiDataTypeVariableKind(var.decl_kind);
  const bool kKept =
      kKind == kVpiReg || kKind == vpiStructVar || kKind == vpiUnionVar;
  return kKept ? 0 : kKind;
}

bool HasFixedElements(const RtlirVariable& var) {
  return var.num_unpacked_dims > 0 && !var.is_queue && !var.is_dynamic &&
         !var.is_assoc && var.unpacked_dims.size() == var.num_unpacked_dims;
}

void AttachArray(VpiObject& array, const std::string& key,
                 const ArrayAttach& attach) {
  AttachLevel({&array, key, {}}, 0, attach);
  RecordDimensionIndices(array, attach.dims);
}

void AttachNetArray(const RtlirNet& net, const std::string& prefix,
                    const VpiObjectMap& objects, const VpiAttachBuild& build) {
  if (net.unpacked_dims.empty() || VpiNetIsInterconnect(net)) return;
  const std::string kKey = VpiFlatName(prefix, net.name);
  VpiObject* array = FindObjectForFlatName(objects, kKey);
  if (array == nullptr) return;
  array->type = vpiNetArray;
  int count = 1;
  for (const RtlirUnpackedDim& dim : net.unpacked_dims) {
    count *= static_cast<int>(dim.Size());
  }
  array->size = count;
  AttachArray(*array, kKey, {net.unpacked_dims, *array, objects, build});
}

struct InterconnectDim {
  PackedRange range;
  bool packed;
};

struct InterconnectShape {
  const std::vector<InterconnectDim>& dims;
  const VpiObjectMap& objects;
  const VpiAttachBuild& build;
};

std::vector<InterconnectDim> InterconnectDims(
    const std::vector<RtlirUnpackedDim>& unpacked, const DataType* type,
    SimContext& ctx) {
  const PackedDims kPacked =
      type != nullptr ? WrittenPackedDims(type, ctx) : PackedDims{};
  std::vector<InterconnectDim> dims;
  dims.reserve(unpacked.size() + kPacked.size());
  for (const RtlirUnpackedDim& dim : unpacked) {
    dims.push_back({PackedRange{dim.left, dim.right}, false});
  }
  for (const PackedRange& dim : kPacked) dims.push_back({dim, true});
  return dims;
}

void AttachInterconnectRanges(VpiObject& level, std::size_t depth,
                              const InterconnectShape& shape) {
  const bool kPacked = shape.dims[depth].packed;
  VpiObject* first = nullptr;
  for (std::size_t d = depth;
       d < shape.dims.size() && shape.dims[d].packed == kPacked; ++d) {
    VpiObject* range = VpiRangeObject(&level, shape.dims[d].range, shape.build);
    if (first == nullptr) first = range;
    level.children.push_back(range);
  }
  level.left_range = first->left_range;
  level.right_range = first->right_range;
}

VpiObject* InterconnectElement(VpiObject& level, const std::string& key,
                               const std::string& suffix,
                               const InterconnectShape& shape) {
  VpiObject* element = FindObjectForFlatName(shape.objects, key);
  if (element == nullptr) {
    element = shape.build.alloc();
    element->name = shape.build.keep(std::string(level.name) + suffix);
    element->full_name = level.full_name + suffix;
  } else {
    std::erase(element->parent->children, element);
  }
  element->parent = &level;
  element->array_member = true;
  level.children.push_back(element);
  return element;
}

void ShapeInterconnectLevel(VpiObject& level, const std::string& key,
                            std::size_t depth, const InterconnectShape& shape) {
  if (depth == shape.dims.size()) {
    level.type = vpiInterconnectNet;
    return;
  }
  const PackedRange& range = shape.dims[depth].range;
  level.type = vpiInterconnectArray;
  level.packed = shape.dims[depth].packed;
  level.size = static_cast<int>(range.HighIndex() - range.LowIndex() + 1);
  AttachInterconnectRanges(level, depth, shape);
  const int64_t kStep = range.left <= range.right ? 1 : -1;
  for (int64_t index = range.left;; index += kStep) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    const std::string kKey = key + kSuffix;
    VpiObject* element = InterconnectElement(level, kKey, kSuffix, shape);
    element->index = static_cast<int>(index);
    ShapeInterconnectLevel(*element, kKey, depth + 1, shape);
    if (index == range.right) break;
  }
}

void ShapeInterconnect(VpiObject& net, const std::string& key,
                       const std::vector<InterconnectDim>& dims,
                       const VpiObjectMap& objects,
                       const VpiAttachBuild& build) {
  if (!dims.empty()) {
    ShapeInterconnectLevel(net, key, 0, {dims, objects, build});
  }
}

int64_t BoundOf(const VpiObject& constant) {
  return static_cast<int32_t>(
      static_cast<uint32_t>(constant.var->value.ToUint64()));
}

VpiObject* SubInterconnectNet(VpiObject& net, std::string_view name,
                              const std::string& suffix,
                              const VpiAttachBuild& build) {
  VpiObject* sub = build.alloc();
  sub->type = vpiInterconnectNet;
  sub->name = name;
  sub->full_name = net.full_name + suffix;
  sub->parent = &net;
  net.children.push_back(sub);
  return sub;
}

void GiveInterconnectTypespec(VpiObject& net, VpiObject* typespec,
                              const VpiAttachBuild& build) {
  if (typespec == nullptr) return;
  net.children.push_back(typespec);
  if (VpiIsInterconnectStructDataTypespec(typespec->type)) {
    for (VpiObject* member : typespec->children) {
      VpiObject* sub = SubInterconnectNet(
          net, member->name, "." + std::string(member->name), build);
      GiveInterconnectTypespec(*sub, VpiTypespecChild(member), build);
    }
    return;
  }
  if (!VpiIsInterconnectArrayDataTypespec(typespec->type)) return;
  const int64_t kLeft = BoundOf(*typespec->left_range);
  const int64_t kRight = BoundOf(*typespec->right_range);
  const int64_t kStep = kLeft <= kRight ? 1 : -1;
  for (int64_t index = kLeft;; index += kStep) {
    const std::string kSuffix = "[" + std::to_string(index) + "]";
    VpiObject* sub = SubInterconnectNet(
        net, build.keep(std::string(net.name) + kSuffix), kSuffix, build);
    sub->index = static_cast<int>(index);
    sub->array_member = true;
    GiveInterconnectTypespec(*sub, typespec->inner_typespec, build);
    if (index == kRight) break;
  }
}

}  // namespace

void VpiRecordWrittenDims(VpiObject& array, const std::vector<Expr*>& dims,
                          SimContext& ctx) {
  std::vector<std::vector<int>> written;
  for (const Expr* dim : dims) {
    const std::optional<PackedRange> kRange = WrittenUnpackedDim(dim, ctx);
    if (!kRange) return;
    std::vector<int>& indices = written.emplace_back();
    const int64_t kStep = kRange->left <= kRange->right ? 1 : -1;
    for (int64_t index = kRange->left; index != kRange->right + kStep;
         index += kStep) {
      indices.push_back(static_cast<int>(index));
    }
  }
  array.array_dim_indices = std::move(written);
}

void AttachArrayElements(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build) {
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
          if (!HasFixedElements(var)) continue;
          const std::string kKey = VpiFlatName(prefix, var.name);
          VpiObject* array = FindObjectForFlatName(objects, kKey);
          if (array == nullptr) continue;
          AttachArray(*array, kKey,
                      {var.unpacked_dims, *array, objects, build,
                       DeclaredElementType(var)});
        }
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          AttachNetArray(net, prefix, objects, build);
        }
      });
}

void AttachInterconnects(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build) {
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        for (const RtlirNet& net : mod->nets) {
          const std::string kKey = VpiFlatName(prefix, net.name);
          VpiObject* obj = FindObjectForFlatName(objects, kKey);
          if (obj == nullptr || !VpiNetIsInterconnect(net)) continue;
          ShapeInterconnect(*obj, kKey,
                            InterconnectDims(net.unpacked_dims, net.dtype, ctx),
                            objects, build);
        }
      });
}

void AttachInterconnectPorts(const RtlirDesign* design,
                             const VpiObjectMap& objects, SimContext& ctx,
                             const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        for (VpiObject* port : instance->children) {
          if (port->type != vpiPort || port->low_conn == nullptr ||
              port->low_conn->type != vpiInterconnectNet) {
            continue;
          }
          const RtlirPort& declared = mod->ports[port->index];
          ShapeInterconnect(
              *port->low_conn, VpiFlatName(prefix, declared.name),
              InterconnectDims(declared.unpacked_dims, declared.dtype, ctx),
              objects, build);
        }
      });
}

void AttachInterconnectTypespecs(const RtlirDesign* design,
                                 const VpiObjectMap& objects,
                                 const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule*, const std::string&, VpiObject* instance) {
        for (VpiObject* net : instance->children) {
          if (net->type != vpiInterconnectNet) continue;
          GiveInterconnectTypespec(
              *net, VpiTypespecChild(VpiMergedTypedNet(net)), build);
        }
      });
}

}  // namespace delta
