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

// §36.12.3: the message an application running under `mode` is given where the
// objects an iteration reached include a construct that mode's standard has no
// notion of, and null where they do not. Defined in vpi_compatibility.cpp,
// called from VpiContext::Iterate, which records it as the §38.2 error.
const char* VpiCompatibilityUnsupportedConstruct(
    int mode, const std::vector<VpiObject*>& objects);

// §36.12.2.2: the iteration a compatibility mode gives an application - the
// current one, with the objects that mode's applications do not expect dropped.
// Defined in vpi_compatibility.cpp, used by vpi.cpp for the run-wide default
// and by the compile-based variants for the mode compiled into them.
vpiHandle VpiIterateInCompatibilityMode(int type, VpiHandle ref, int mode);

// Defined in vpi_systf.cpp, used by vpi_handle.cpp.
std::vector<std::string_view> VpiNamePathComponents(std::string_view name);

}  // namespace delta
