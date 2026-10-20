#pragma once

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// §38.15 with §37.31, §37.17, §37.26 and §37.36: whether vpi_get_value() of
// `obj` in the format `value` asks for is refused, the error then recorded in
// `error` and the caller's buffer left untouched.
bool VpiGetValueIsRefused(VpiHandle obj, const s_vpi_value& value,
                          s_vpi_error_info& error);

// §38.34 with §37.31, §37.17, §37.26, §37.35, §37.3.5 and §6.6.7: whether
// vpi_put_value() to `obj` is refused whatever its delay mode, the error then
// recorded in `error` and the target left unchanged.
bool VpiPutValueTargetIsRejected(VpiHandle obj, s_vpi_error_info& error);

}  // namespace delta
