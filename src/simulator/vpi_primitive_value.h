#pragma once

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

class SimContext;

VpiHandle VpiPrimitiveValueSource(VpiHandle obj);

bool VpiPutSequentialUdpValue(const VpiObject& obj, const s_vpi_value* value,
                              SimContext* sim);

}  // namespace delta
