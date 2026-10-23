#pragma once

// §39.4.2: placing an assertion callback and removing it again - the two
// operations vpi_register_assertion_cb() and vpi_remove_cb() perform on an
// assertion. They are declared here rather than beside the other VPI entry
// points because they are where two models meet: the object model of
// simulator/vpi_context.h, which is what a handle names, and the assertion
// model of simulator/dpi_runtime.h, which is where clause 39's rules about
// which callbacks may be placed and what a placed callback is handed are
// written.

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// §39.3.1: the key the assertion model keeps the assertion `obj` under, one
// per instance of one assertion: its full name where it has one, the name a
// hand-built object was given otherwise, and for an unnamed assertion its
// scope and the place it starts at (AssertionKey).
std::string VpiAssertionKeyOf(const VpiObject& obj);

// §39.3.1 with §9.3.5: the object a full name that resolved to `found` names.
// A label on an assertion written in a procedure also opens a named begin
// around it whose full name is the assertion's own; that name answers the
// assertion, the begin staying the scope names below it resolve through. Any
// other object answers itself.
VpiHandle VpiLabelledAssertionOr(VpiHandle found);

// D.11 with §9.3.5: the scope `found` stands as when its name is taken as a
// scope's. An assertion VpiLabelledAssertionOr answered for the full name of
// the named begin its label opens stands as that begin; any other object
// stands as itself.
VpiHandle VpiLabelledAssertionsBeginOr(VpiHandle found);

// §39.4.2: place `cb_rtn` on `assertion` for `reason`, with `user_data` carried
// through to every call of it. A placement that succeeds answers a handle to
// the callback, and one that fails answers NULL: no assertion, no routine to
// call, or a reason that may not be placed on an assertion of that kind are
// those errors.
VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func* cb_rtn,
                                 PLI_BYTE8* user_data);

// §39.4.2: vpi_remove_cb() removes a callback by the handle its placement
// answered. True when `cb_handle` was such a handle and the placement
// it named was removed, which is what tells vpi_remove_cb() that the handle was
// an assertion callback's rather than a simulation callback's.
bool VpiRemoveAssertionCb(VpiHandle cb_handle);

}  // namespace delta
