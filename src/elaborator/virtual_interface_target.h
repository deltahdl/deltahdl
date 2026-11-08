#pragma once

#include <functional>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleDecl;

void ValidateVirtualInterfaceTarget(const DataType& type, SourceLoc loc,
                                    const ModuleDecl* iface_decl,
                                    DiagEngine& diag);

void ValidateVirtualInterfaceType(
    const DataType& type, SourceLoc loc,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag);

}  // namespace delta
