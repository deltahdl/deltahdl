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

// One level of an array var being given its members: the object they hang
// from, the flat key and the full name that object is reached by, and the
// indices that selected it out of the array, outermost first.
struct ArrayLevel {
  VpiObject* holder;
  std::string key;
  std::vector<int64_t> indices;
};

// What attaching one array var's members reads: the declaration's unpacked
// dimensions, the array object every subarray copies its kind from, and the
// model to find the elements in and to build in.
struct ArrayAttach {
  const std::vector<RtlirUnpackedDim>& dims;
  const VpiObject& array;
  const VpiObjectMap& objects;
  const VpiAttachBuild& build;
  // The kind each element stands as where the array's declaration says it,
  // zero to leave the kind the run's object for the element has.
  int element_type = 0;
};

// The indices of one dimension in the order it declares them, left first.
std::vector<int64_t> IndicesOf(const RtlirUnpackedDim& dim) {
  std::vector<int64_t> indices;
  const int64_t kStep = dim.left <= dim.right ? 1 : -1;
  for (int64_t i = dim.left;; i += kStep) {
    indices.push_back(i);
    if (i == dim.right) break;
  }
  return indices;
}

// §37.17 details 2, 18 and 26: `member` made the member of `level.holder` at
// `index`: its vpiParent is the holder, it carries its index for vpiIndex and
// an index select (§38.19), and its vpiIndex iteration reaches the indices
// that select it out of the array, starting with its own and working outward.
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

// The members of the array at `level`, one per index of dimension `depth`: the
// elements the run keyed under the array's name at the innermost dimension,
// and a subarray, an array var of its own, at every other.
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
      // §37.17 detail 20: the array answers vpiScalar and vpiVector as its
      // element does (RecordVariableFacts), so the element answers alike.
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

// §38.16 and §38.35: the indices each unpacked dimension of `array` declares,
// left first, from which vpi_get_value_array and vpi_put_value_array find
// the flat ordinal of the element a coordinate names.
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

// The kind an element of the array `var` stands as where its declaration says
// it, zero where the run's object for the element says it. §37.17 with
// §37.33: an element of an array of class handles is a class var, and §37.12
// detail 7 with §37.29: an element of an array of virtual interfaces is a
// virtual interface var, which the run made a reg like every element. §37.17
// (printed page 1025) makes an element of an array of any other built-in type
// a variable of that type, an int var of `int a[4]`, and §37.27 an element of
// an event array a named event. An element of a structure or union array
// keeps the reg the run made it, which its bits are indexed as (VarBitDims).
int DeclaredElementType(const RtlirVariable& var) {
  if (!var.class_type_name.empty()) return vpiClassVar;
  const int kKind = VpiDataTypeVariableKind(var.decl_kind);
  const bool kKept =
      kKind == kVpiReg || kKind == vpiStructVar || kKind == vpiUnionVar;
  return kKept ? 0 : kKind;
}

// Whether `var` is an array var whose every unpacked dimension is fixed, the
// arrays whose elements the run keys under the array's name.
bool HasFixedElements(const RtlirVariable& var) {
  return var.num_unpacked_dims > 0 && !var.is_queue && !var.is_dynamic &&
         !var.is_assoc && var.unpacked_dims.size() == var.num_unpacked_dims;
}

// The members of the array `array`, keyed `key`, hung from it one unpacked
// dimension of `attach.dims` at a time.
void AttachArray(VpiObject& array, const std::string& key,
                 const ArrayAttach& attach) {
  AttachLevel({&array, key, {}}, 0, attach);
  RecordDimensionIndices(array, attach.dims);
}

// §37.16 details 1, 2 and 24: a net declared with an unpacked dimension is an
// array net, each net in it is an array member whose vpiParent is the array
// net, and the array net's vpiSize is the number of nets it holds. The run
// keys each element net under `n[i]` beside the array, as it does an array
// var's elements, so the array net stood as a net of its own and its elements
// as its siblings. A generic interconnect is shaped apart (ShapeInterconnect).
void AttachNetArray(const RtlirNet& net, const std::string& prefix,
                    const VpiObjectMap& objects, const VpiAttachBuild& build) {
  if (net.unpacked_dims.empty() || VpiNetIsInterconnect(net)) return;
  const std::string kKey = VpiFlatName(prefix, net.name);
  VpiObject* array = FindObjectForFlatName(objects, kKey);
  // A net standing for an enclosing module's (§23.4) has no object here.
  if (array == nullptr) return;
  array->type = vpiNetArray;
  int count = 1;
  for (const RtlirUnpackedDim& dim : net.unpacked_dims) {
    count *= static_cast<int>(dim.Size());
  }
  array->size = count;
  AttachArray(*array, kKey, {net.unpacked_dims, *array, objects, build});
}

// One dimension of a generic interconnect, which §37.24 draws as a level of
// interconnect arrays, packed where the declaration wrote it before the name.
struct InterconnectDim {
  PackedRange range;
  bool packed;
};

// One generic interconnect being shaped: its dimensions, the unpacked ones
// outermost and the packed ones inside them (§7.4), the run's objects to take
// an element from, and the model to build in.
struct InterconnectShape {
  const std::vector<InterconnectDim>& dims;
  const VpiObjectMap& objects;
  const VpiAttachBuild& build;
};

// The dimensions of an interconnect declared with the unpacked dimensions
// `unpacked` and the packed ones `type` writes (§6.6.8), none for a null type.
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

// §37.24 (figure): the ranges of the interconnect array `level` that the
// dimensions from `depth` on make - one per dimension of the kind of the first,
// as an array var's are its unpacked dimensions or else its packed ones
// (§37.17 detail 4) - and the bounds of the first, its vpiLeftRange and
// vpiRightRange.
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

// The element of `level` that `suffix` selects: the run's net keyed `key`,
// moved under `level`, or one made for it and named after it.
VpiObject* InterconnectElement(VpiObject& level, const std::string& key,
                               const std::string& suffix,
                               const InterconnectShape& shape) {
  VpiObject* element =
      key.empty() ? nullptr : FindObjectForFlatName(shape.objects, key);
  if (element == nullptr) {
    element = shape.build.alloc();
    element->name = shape.build.keep(std::string(level.name) + suffix);
    if (!level.full_name.empty()) element->full_name = level.full_name + suffix;
  } else {
    std::erase(element->parent->children, element);
  }
  element->parent = &level;
  element->array_member = true;
  level.children.push_back(element);
  return element;
}

// §37.24 details 1 and 2 with §6.6.8: `level`, keyed `key` where the run keeps
// objects under it, made the interconnect array of the dimensions from `depth`
// on, whose vpiSize is the number of elements of the first and whose
// vpiElement iteration reaches an element per index of it, or, past the last
// dimension, an interconnect net.
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
    const std::string kKey = key.empty() ? std::string() : key + kSuffix;
    VpiObject* element = InterconnectElement(level, kKey, kSuffix, shape);
    element->index = static_cast<int>(index);
    ShapeInterconnectLevel(*element, kKey, depth + 1, shape);
    if (index == range.right) break;
  }
}

// The generic interconnect `net`, keyed `key` where the run keeps objects
// under it, given the dimensions `dims`; left as it is where it has none.
void ShapeInterconnect(VpiObject& net, const std::string& key,
                       const std::vector<InterconnectDim>& dims,
                       const VpiObjectMap& objects,
                       const VpiAttachBuild& build) {
  if (!dims.empty()) {
    ShapeInterconnectLevel(net, key, 0, {dims, objects, build});
  }
}

// The value of a range's bound, a 32-bit integer constant (VpiIntConstant).
int64_t BoundOf(const VpiObject& constant) {
  return static_cast<int32_t>(
      static_cast<uint32_t>(constant.var->value.ToUint64()));
}

// An interconnect net under the interconnect net `net`, named `name`, whose
// full name is the net's with `suffix` after it.
VpiObject* SubInterconnectNet(VpiObject& net, std::string_view name,
                              const std::string& suffix,
                              const VpiAttachBuild& build) {
  VpiObject* sub = build.alloc();
  sub->type = vpiInterconnectNet;
  sub->name = name;
  if (!net.full_name.empty()) sub->full_name = net.full_name + suffix;
  sub->parent = &net;
  net.children.push_back(sub);
  return sub;
}

// §37.24 detail 1: the interconnect net `net` takes `typespec`, that of what it
// is connected to, none where nothing is, and with it an interconnect net per
// member of a struct or union typespec, reached through vpiMember, or per
// element of an array typespec's first dimension, reached through vpiElement,
// each taking the typespec of its member or element in turn.
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
  // §37.17 details 2, 18 and 26: each element of an array var is a member of
  // the array, and a multidimensional array's subarrays are array vars of their
  // own. The run keyed each element under `arr[i]` beside the array, so it
  // stood in the scope as the array's sibling and no index reached it. An
  // array net's nets are hung from it the same way (§37.16 detail 2).
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
  // §37.24 details 1 and 2: a generic interconnect's every dimension is a
  // level of interconnect arrays, its packed ones among them. Only an unpacked
  // dimension made one, and of a body interconnect only the first: the
  // interconnect nets below a second, which the run keys no net under, were
  // left logic nets, and a packed dimension made bits.
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
              *port->low_conn, std::string(),
              InterconnectDims(declared.unpacked_dims, declared.dtype, ctx),
              objects, build);
        }
      });
}

void AttachInterconnectTypespecs(const RtlirDesign* design,
                                 const VpiObjectMap& objects,
                                 const VpiAttachBuild& build) {
  // §37.24 detail 1: an interconnect net's typespec is that of the net it is
  // connected to. None was given one, so vpiTypespec of an interconnect net
  // was null and its vpiElement and vpiMember iterations reached nothing.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule*, const std::string&, VpiObject* instance) {
        for (VpiObject* net : instance->children) {
          if (net->type != vpiInterconnectNet) continue;
          GiveInterconnectTypespec(*net, VpiTypespecChild(VpiConnectedNet(net)),
                                   build);
        }
      });
}

}  // namespace delta
