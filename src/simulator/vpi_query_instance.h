#pragma once

#include "simulator/vpi_object.h"

namespace delta {

bool VpiGetInstanceProperty(int property, VpiHandle obj, int& value);

}  // namespace delta
