#pragma once

// §39.4.2: placing an assertion callback and removing it again - the two
// operations vpi_register_assertion_cb() and vpi_remove_cb() perform on an
// assertion. They are declared here rather than beside the other VPI entry
// points because they are where two models meet: the object model of
// simulator/vpi_context.h, which is what a handle names, and the assertion
// model of simulator/dpi_runtime.h, which is where clause 39's rules about
// which callbacks may be placed and what a placed callback is handed are
// written.

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

namespace delta {

// §39.4.2: place `cb_rtn` on `assertion` for `reason`, with `user_data` carried
// through to every call of it. "If the callback is successfully placed, a
// handle to the callback is returned ... If there were errors on placing the
// callback, a NULL handle is returned": no assertion, no routine to call, or a
// reason that may not be placed on an assertion of that kind are those errors.
VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func cb_rtn,
                                 PLI_BYTE8* user_data);

// §39.4.2: "This handle can be used to remove the callback via
// vpi_remove_cb()." True when `cb_handle` was such a handle and the placement
// it named was removed, which is what tells vpi_remove_cb() that the handle was
// an assertion callback's rather than a simulation callback's.
bool VpiRemoveAssertionCb(VpiHandle cb_handle);

}  // namespace delta
