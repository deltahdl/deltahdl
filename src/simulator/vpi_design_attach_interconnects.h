#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

void AttachInterconnects(const RtlirDesign* design, const VpiObjectMap& objects,
                         SimContext& ctx, const VpiAttachBuild& build);

void AttachInterconnectPorts(const RtlirDesign* design,
                             const VpiObjectMap& objects, SimContext& ctx,
                             const VpiAttachBuild& build);

void AttachInterconnectTypespecs(const RtlirDesign* design,
                                 const VpiObjectMap& objects,
                                 const VpiAttachBuild& build);

}  // namespace delta
