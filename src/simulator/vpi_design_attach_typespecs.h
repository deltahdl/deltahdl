#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

// §37.14 (figure): relate each port of the design's instances to the
// typespec of the type its declaration wrote, its dimensions evaluated in the
// instance through `ctx`, a typedef's among those its instance declares or
// `outer`, the compilation unit's and the packages' AttachTypespecs answered,
// and a class's reaching its defn among `classes`. Runs once the ports are
// objects.
void AttachPortTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiObjectMap& outer,
                         const VpiClassDefnObjects& classes, SimContext& ctx,
                         const VpiAttachBuild& build);

}  // namespace delta
