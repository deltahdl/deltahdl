#pragma once

#include <vector>

#include "simulator/vpi_object.h"

namespace delta {

const std::vector<VpiObject*>* VpiConstraintListOf(int type,
                                                   const VpiObject* ref);

bool VpiTryResolveConstraintRelation(int type, VpiHandle ref, VpiHandle& out);

}  // namespace delta
