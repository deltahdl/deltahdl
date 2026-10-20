#pragma once

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

// §37.22 detail 1: give `range`, the first range of a dynamic array or queue,
// the two integer constants its bounds are read through once the array holds
// elements, as its children; it holds none at the start of simulation, so
// its vpiLeftRange and vpiRightRange stay null.
void VpiGiveDynamicRangeBounds(VpiObject& range, const VpiAttachBuild& build);

// §37.22 detail 1: the range of a dynamic array or queue whose bounds follow
// the elements the run's store of it holds now, the one
// VpiGiveDynamicRangeBounds gave its bounds: `obj` itself where it is that
// range and the first range of `obj` where it is such an array; null for any
// other object, the range of an associative dimension and of a fixed one among
// them.
VpiHandle VpiDynamicRangeOf(VpiHandle obj);

// §37.22 details 1 and 2: the vpiSize of the range `range`, which
// VpiDynamicRangeOf answers for itself, the number of elements its array holds
// now, 0 while it is empty.
int VpiDynamicRangeSize(const VpiObject& range);

// §37.22 details 1 and 2 with §37.17 detail 6: the bound `type`, vpiLeftRange
// or vpiRightRange, of the range `range`, which VpiDynamicRangeOf answers for
// itself: 0 and n-1 over the n elements its array holds now, and null while it
// holds none.
VpiHandle VpiDynamicRangeBound(int type, const VpiObject& range);

}  // namespace delta
