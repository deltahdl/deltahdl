#pragma once

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct DataType;
struct RtlirDesign;

VpiObject* VpiKeywordTypespec(const DataType& type, VpiObject* parent,
                              SimContext& ctx, const VpiAttachBuild& build);

void AttachPortTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiCallObjects& calls, SimContext& ctx,
                         const VpiAttachBuild& build);

}  // namespace delta
