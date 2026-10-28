#pragma once

#include <functional>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleDecl;

// §25.9: the rules on the interface a virtual interface type `type`, written
// at `loc`, names, `find_module` resolving the name from where the type is
// written: it is an interface, the modport the type selects is one that
// interface declares, and the interface refers to no object outside its body.
// A type of any other kind is not judged.
void ValidateVirtualInterfaceType(
    const DataType& type, SourceLoc loc,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag);

}  // namespace delta
