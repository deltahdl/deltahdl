#pragma once

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiGetValueIsRefused(VpiHandle obj, const s_vpi_value& value,
                          s_vpi_error_info& error);

bool VpiPutValueTargetIsRejected(VpiHandle obj, s_vpi_error_info& error);

}  // namespace delta
