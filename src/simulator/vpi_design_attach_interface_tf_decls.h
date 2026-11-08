#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

void AttachInterfaceTfDecls(const RtlirDesign* design,
                            const VpiObjectMap& objects,
                            const VpiSubroutineObjects& made, SimContext& ctx,
                            const VpiAttachBuild& build);

}  // namespace delta
