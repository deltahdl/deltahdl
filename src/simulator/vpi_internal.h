#pragma once

#include <string_view>
#include <vector>

#include "simulator/vpi.h"

// Internal helpers shared between the vpi.cpp translation units. These are file
// scoped helpers that were promoted from anonymous/static linkage so that the
// definition in one translation unit can be reused by another. They are not
// part of the public VPI surface declared in vpi.h.
namespace delta {

// Defined in vpi_helpers_statements.cpp, used by vpi_callbacks.cpp.
bool VpiIsScopeBodyStmtType(int type);

// Defined in vpi_helpers_statements.cpp, used by vpi_iterate.cpp.
bool VpiIsVirtualInterfaceArray(VpiHandle obj);

// Defined in vpi_systf.cpp, used by vpi_helpers_statements.cpp,
// vpi_handle.cpp, and vpi_value.cpp.
bool VpiObjectIsPrimitive(int type);

// Defined in vpi_systf.cpp, used by vpi_handle.cpp.
std::vector<std::string_view> VpiNamePathComponents(std::string_view name);

}  // namespace delta
