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

// §37.63/§37.66/§37.67/§37.70: the kinds that reach a body statement through
// the object model's untagged arrow to `stmt`. Defined in
// vpi_helpers_statements.cpp, used by vpi_handle.cpp.
bool VpiIsBodyStmtOwnerType(int type);

// §37.73: the else action of an expect statement - the second of the two
// statements it carries. Defined in vpi_helpers_statements.cpp, used by
// vpi_handle.cpp.
VpiHandle VpiExpectElseStmt(VpiHandle expect);

// §37.74: the first of the initialization or increment statements a for
// statement's header writes, which the diagram's single arrow reaches. Defined
// in vpi_helpers_loops.cpp, used by vpi_handle.cpp.
VpiHandle VpiForHeaderStmt(int type, VpiHandle for_stmt);

// §37.74: every one of them, which the diagram's double arrow walks. Defined in
// vpi_helpers_loops.cpp, used by vpi_iterate.cpp.
void VpiCollectForHeaderStmts(int type, VpiHandle for_stmt, VpiHandle iter);

// §37.63/§37.66/§37.67/§37.70/§37.71/§37.73/§37.74/§37.75: the body statement
// the object model draws an untagged arrow to `stmt` for, §37.74's two single
// arrows to a for statement's header, and the process a statement runs in.
// Defined in vpi_handle_statements.cpp, used by vpi_handle.cpp.
bool TryResolveProcessAndStmtRelation(int type, VpiHandle ref, VpiHandle& out);

// §37.80 (figure): whether an object is one of the kinds the callback diagram
// draws a single arrow from to `callback`. Defined in vpi_callbacks.cpp, used
// by vpi_handle.cpp.
bool VpiIsCallbackHostType(int type);

// §37.80 (figure) + detail 2: the callback objects an iteration reaches - those
// registered on `ref`, or, with no reference object, those no object the
// diagram draws that arrow from reaches. Defined in vpi_callbacks.cpp, used by
// vpi_iterate.cpp.
void VpiCollectCallbackObjects(VpiHandle ref,
                               const std::vector<VpiHandle>& cb_handles,
                               const std::vector<VpiCbData>& callbacks,
                               VpiHandle iter);

// Defined in vpi_helpers_statements.cpp, used by vpi_iterate.cpp.
bool VpiIsVirtualInterfaceArray(VpiHandle obj);

// §39.3.1 step b: the assertions of one instance - every assertion written
// anywhere in its body, and none of those belonging to an instance nested
// inside it. Defined in vpi_helpers_instance.cpp, used by vpi_iterate.cpp.
void VpiCollectInstanceAssertions(VpiHandle scope, VpiHandle iter);

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
