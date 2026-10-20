#pragma once

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct RtlirDesign;
struct RtlirVariable;

// §37.18 detail 1: whether the variable `var` is a packed array var, a packed
// array of a packed struct, union or enum: a variable of such a type, named or
// written in place, declared with a packed dimension of its own. An enum
// written in place holds its base type's range where such a dimension is held,
// so a variable of one is none.
bool VpiVariableIsPackedArray(const RtlirVariable& var);

// §37.16 detail 32 and §37.18 detail 3: make the subelements of each packed
// array net and packed array var of `design`, which is not null, one packed
// dimension at a time down to its struct, union or enum nets or vars, which
// its vpiElement iteration reaches.
void AttachPackedArrayElements(const RtlirDesign* design,
                               const VpiObjectMap& objects, SimContext& ctx,
                               const VpiAttachBuild& build);

// §37.16 detail 32, §37.18 detail 3 and §37.26: give each struct or union
// subelement of each packed array net and packed array var of `design`, which
// is not null, a member per field of its type, holding that field's bits of
// the subelement.
void AttachPackedArrayMembers(const RtlirDesign* design,
                              const VpiObjectMap& objects, SimContext& ctx,
                              const VpiAttachBuild& build);

}  // namespace delta
