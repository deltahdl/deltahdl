#pragma once

#include <string_view>

#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

struct RtlirModule;

// Maps a net data-type kind to its RTLIR net type, defaulting to kWire for any
// kind that is not a net type. Defined once in elaborator_decls.cpp and shared
// by the translation units that lower net declarations and validate operations.
NetType DataTypeToNetType(DataTypeKind kind);

// Shared file-local helper for the elaborator_items translation units: a name
// is "declared" in a module if it matches any variable, net, or port already
// recorded on the module. Defined once in elaborator_items.cpp; used there and
// by the module-instantiation/port-binding and generate translation units.
bool IsNameDeclared(std::string_view name, const RtlirModule* mod);

}  // namespace delta
