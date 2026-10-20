#include "simulator/vpi_dynamic_ranges.h"

#include <cstdint>

#include "common/types.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// Whether `array` is a dynamic array or a queue, the only variables the run
// keeps a store of elements for (RecordArrayFacts).
bool IsDynamicArray(const VpiObject& array) { return array.queue != nullptr; }

}  // namespace

void VpiGiveDynamicRangeBounds(VpiObject& range, const VpiAttachBuild& build) {
  range.children.push_back(VpiIntConstant(0, build));
  range.children.push_back(VpiIntConstant(0, build));
}

VpiHandle VpiDynamicRangeOf(VpiHandle obj) {
  if (obj->type == vpiRange) {
    const VpiObject* array = obj->parent;
    const bool kDynamic =
        array != nullptr && IsDynamicArray(*array) && obj->children.size() == 2;
    return kDynamic ? obj : nullptr;
  }
  if (!IsDynamicArray(*obj)) return nullptr;
  // §37.17 detail 4: the first range is the leftmost dimension's.
  for (VpiObject* child : obj->children) {
    if (child->type == vpiRange) return VpiDynamicRangeOf(child);
  }
  return nullptr;
}

int VpiDynamicRangeSize(const VpiObject& range) {
  return static_cast<int>(range.parent->queue->elements.size());
}

VpiHandle VpiDynamicRangeBound(int type, const VpiObject& range) {
  const int kSize = VpiDynamicRangeSize(range);
  if (kSize == 0) return nullptr;
  if (type == vpiLeftRange) return range.children[0];
  VpiObject* right = range.children[1];
  right->var->value.words[0] = Logic4Word{static_cast<uint32_t>(kSize - 1), 0};
  return right;
}

}  // namespace delta
