#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;
struct RtlirVariable;

bool VpiVariableIsPackedArray(const RtlirVariable& var);

void AttachPackedArrayElements(const RtlirDesign* design,
                               const VpiObjectMap& objects, SimContext& ctx,
                               const VpiAttachBuild& build);

void AttachPackedArrayMembers(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

}  // namespace delta
