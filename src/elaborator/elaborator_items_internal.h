#pragma once

#include <string_view>

namespace delta {

struct RtlirModule;

// Shared file-local helper for the elaborator_items translation units: a name
// is "declared" in a module if it matches any variable, net, or port already
// recorded on the module. Defined once in elaborator_items.cpp; used there and
// by the module-instantiation/port-binding and generate translation units.
bool IsNameDeclared(std::string_view name, const RtlirModule* mod);

}  // namespace delta
