#pragma once

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct DataType;
struct RtlirDesign;

// §37.23 (figure): the typespec of the data type `type` a nettype declaration
// `decl` of the scope `scope` declares: the typespec of the typedef a name
// finds among the scope's typespecs, and otherwise one of the type's keyword
// kind hung from `decl`, over the packed ranges written, evaluated through
// `ctx`; for a nettype declared as an alias, the typespec of the nettype it
// aliases; null for a name neither a typedef nor a nettype of the scope
// declares.
VpiObject* VpiNettypeTypespec(const DataType& type, const VpiObject& scope,
                              VpiObject* decl, SimContext& ctx,
                              const VpiAttachBuild& build);

// §37.14 (figure): relate each port of the design's instances to the
// typespec of the type its declaration wrote, its dimensions evaluated in the
// instance through `ctx`, a typedef's among those its instance declares or
// the `calls` unit typespecs, the compilation unit's and the packages'
// AttachTypespecs answered, and a class's reaching its defn among the `calls`
// classes. Runs once the ports are objects.
void AttachPortTypespecs(const RtlirDesign* design, const VpiObjectMap& objects,
                         const VpiCallObjects& calls, SimContext& ctx,
                         const VpiAttachBuild& build);

}  // namespace delta
