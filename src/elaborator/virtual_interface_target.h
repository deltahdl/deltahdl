#pragma once

#include <functional>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleDecl;

// §25.9: the rules on the interface the virtual interface type `type`, written
// at `loc`, names, `iface_decl` being the declaration its name finds from
// there, null for none: it is an interface, the modport the type selects is
// one that interface declares, and the interface refers to no object outside
// its body.
void ValidateVirtualInterfaceTarget(const DataType& type, SourceLoc loc,
                                    const ModuleDecl* iface_decl,
                                    DiagEngine& diag);

// The same for a declared type of any kind, `find_module` resolving a virtual
// interface type's name from where it is written; a type of any other kind is
// not judged.
void ValidateVirtualInterfaceType(
    const DataType& type, SourceLoc loc,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag);

}  // namespace delta
