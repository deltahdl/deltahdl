#pragma once

#include <functional>
#include <string>
#include <string_view>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct DataType;
struct ModuleDecl;
struct RtlirDesign;
struct RtlirModule;
struct VpiObject;

const ModuleDecl* VpiVirtualInterfaceOf(const RtlirDesign& design,
                                        const DataType* type,
                                        const RtlirModule* mod);

VpiObject* VpiVirtualInterfaceClockingBlock(
    VpiObject* holder, std::string_view written,
    const std::function<VpiObject*()>& alloc, const VpiNameKeeper& keep);

void VpiRefreshVirtualInterfaceActual(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name);

void VpiRefreshPrefixedClockingBlock(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name);

}  // namespace delta
