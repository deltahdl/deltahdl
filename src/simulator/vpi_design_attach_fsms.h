#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

void AttachFsms(const RtlirDesign* design, const VpiObjectMap& objects,
                SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
