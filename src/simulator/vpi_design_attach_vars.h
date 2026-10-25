#pragma once

#include <cstdint>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct DataType;
struct RtlirDesign;
struct StructTypeInfo;

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

// §37.17 details 12 and 26: give `var`, a variable of the data type `type`
// that is `width` bits wide and is held in no storage of the run's, a var bit
// per bit of the packed dimensions `type` declares, evaluated in `ctx`, where
// `var` is a logic or bit variable or a packed array of them. A local
// variable of a sequence or property is such a variable, its value having no
// access (§37.52 detail 1).
void VpiMakeVarBits(VpiObject& var, const DataType& type, uint32_t width,
                    SimContext& ctx, const VpiAttachBuild& build);

// §37.17 details 3, 17 and 26: give `local`, the struct or union var a local
// variable of a sequence or property stands as, a member variable per field
// of `layout`, a type name a field is written with resolving in the run's
// type table in `ctx`. The members, as the local, stand in no instance's
// storage (§37.52 detail 1).
void VpiMakeLocalMembers(VpiObject* local, const StructTypeInfo& layout,
                         SimContext& ctx, const VpiAttachBuild& build);

}  // namespace delta
