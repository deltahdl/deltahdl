#pragma once

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

void VpiGiveDynamicRangeBounds(VpiObject& range, const VpiAttachBuild& build);

VpiHandle VpiDynamicRangeOf(VpiHandle obj);

int VpiDynamicRangeSize(const VpiObject& range);

VpiHandle VpiDynamicRangeBound(int type, const VpiObject& range);

}  // namespace delta
