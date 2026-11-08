#pragma once

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

std::string VpiAssertionKeyOf(const VpiObject& obj);

VpiHandle VpiLabelledAssertionOr(VpiHandle found);

VpiHandle VpiLabelledAssertionsBeginOr(VpiHandle found);

VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func* cb_rtn,
                                 PLI_BYTE8* user_data);

bool VpiRemoveAssertionCb(VpiHandle cb_handle);

}  // namespace delta
