#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;

// §37.17 detail 8: give each variable an instance of `design` declares with an
// initialization expression that expression, built in the instance's own
// scope, which vpi_handle(vpiExpr) of the variable reaches.
void AttachVariableInitializers(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build);

// §37.17 detail 12: give the struct or union member `member` a var bit per
// bit of `dims`, as a packed variable has, each read from the storage of the
// outermost structure `member` is a member of, at the member's offset there.
void VpiMakeMemberBits(VpiObject& member, const PackedDims& dims,
                       const VpiAttachBuild& build);

}  // namespace delta
