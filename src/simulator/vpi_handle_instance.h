#pragma once

#include "simulator/vpi_object.h"

namespace delta {

bool TryResolveInstanceRelation(int type, VpiHandle ref, VpiHandle& out);

}  // namespace delta
