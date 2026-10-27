#pragma once

#include <cstdint>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct DataType;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
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

// §36.12.1 Table 36-10 rows 3, 4 and 7: the object kind an elaborated variable
// carries. In the IEEE 1800 standards those arrays are always vpiRegArray
// objects while vpiIntegerVar and vpiTimeVar objects are never arrays, a real
// array is a vpiRegArray object and nothing else, and so a vpiRegArray
// iteration takes in arrays of integer, time and real variables. So an unpacked
// array is one kind whatever it holds, and every other variable is the kind it
// was declared: through a typedef name, the kind of the type at the end of its
// chain (§6.18), which `design` records and `mod` may declare a class under.
int VpiVariableObjectKind(const RtlirVariable& var, const RtlirDesign& design,
                          const RtlirModule& mod);

// §37.17 with §26.2 and §3.12.1: tell each variable a package of `design` or
// its compilation unit declares, among `objects` under the package's name or
// the unit's scope name, the kind its declaration makes it, with the facts
// read off the declaration and the run `ctx` alongside, as the variables of an
// instance are told theirs. VpiContext::Attach stamps every variable vpiReg,
// and the instances' pass reaches none of these.
void VpiRecordScopeVariableKinds(const RtlirDesign& design,
                                 const VpiObjectMap& objects, SimContext& ctx);

}  // namespace delta
