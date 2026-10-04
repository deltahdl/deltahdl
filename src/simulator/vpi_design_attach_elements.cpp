#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

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
      if (element != nullptr) Adopt(element, level, index, attach.build);
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

// Whether `var` is an array var whose every unpacked dimension is fixed, the
// arrays whose elements the run keys under the array's name.
bool HasFixedElements(const RtlirVariable& var) {
  return var.num_unpacked_dims > 0 && !var.is_queue && !var.is_dynamic &&
         !var.is_assoc && var.unpacked_dims.size() == var.num_unpacked_dims;
}

}  // namespace

void AttachArrayElements(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiAttachBuild& build) {
  // §37.17 details 2, 18 and 26: each element of an array var is a member of
  // the array, and a multidimensional array's subarrays are array vars of their
  // own. The run keyed each element under `arr[i]` beside the array, so it
  // stood in the scope as the array's sibling and no index reached it.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : mod->variables) {
          if (!HasFixedElements(var)) continue;
          const std::string kKey = VpiFlatName(prefix, var.name);
          VpiObject* array = FindObjectForFlatName(objects, kKey);
          if (array == nullptr) continue;
          const ArrayAttach kAttach{var.unpacked_dims, *array, objects, build};
          AttachLevel({array, kKey, {}}, 0, kAttach);
        }
      });
}

}  // namespace delta
