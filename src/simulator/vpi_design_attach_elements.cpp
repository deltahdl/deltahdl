#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
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
// as its siblings. §37.24 details 1 and 2 make a generic interconnect so
// declared an interconnect array instead, whose vpiSize is the number of
// elements of its first dimension, each a further interconnect array down to
// the interconnect nets of the last.
void AttachNetArray(const RtlirNet& net, const std::string& prefix,
                    const VpiObjectMap& objects, const VpiAttachBuild& build) {
  if (net.unpacked_dims.empty()) return;
  const std::string kKey = VpiFlatName(prefix, net.name);
  VpiObject* array = FindObjectForFlatName(objects, kKey);
  // A net standing for an enclosing module's (§23.4) has no object here.
  if (array == nullptr) return;
  const bool kInterconnect = net.net_type == NetType::kInterconnect;
  array->type = kInterconnect ? vpiInterconnectArray : vpiNetArray;
  int count = 1;
  for (const RtlirUnpackedDim& dim : net.unpacked_dims) {
    count *= static_cast<int>(dim.Size());
  }
  array->size =
      kInterconnect ? static_cast<int>(net.unpacked_dims[0].Size()) : count;
  AttachArray(*array, kKey, {net.unpacked_dims, *array, objects, build});
}

}  // namespace

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
          // §37.17 with §37.33: an element of an array of class handles is a
          // class var, which the run made a reg like every element.
          AttachArray(*array, kKey,
                      {var.unpacked_dims, *array, objects, build,
                       var.class_type_name.empty() ? 0 : vpiClassVar});
        }
        for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
          AttachNetArray(net, prefix, objects, build);
        }
      });
}

}  // namespace delta
