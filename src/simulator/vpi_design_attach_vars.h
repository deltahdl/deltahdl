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

void AttachVariableInitializers(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build);

void VpiMakeMemberBits(VpiObject& member, const PackedDims& dims,
                       const VpiAttachBuild& build);

void VpiMakeVarBits(VpiObject& var, const DataType& type, uint32_t width,
                    SimContext& ctx, const VpiAttachBuild& build);

void VpiMakeLocalMembers(VpiObject* local, const StructTypeInfo& layout,
                         SimContext& ctx, const VpiAttachBuild& build);

int VpiVariableObjectKind(const RtlirVariable& var, const RtlirDesign& design,
                          const RtlirModule& mod);

void VpiRecordScopeVariableKinds(const RtlirDesign& design,
                                 const VpiObjectMap& objects, SimContext& ctx);

}  // namespace delta
