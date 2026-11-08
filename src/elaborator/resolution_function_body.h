#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleItem;

void CheckResolutionFunctionBody(const ModuleItem* fn, DiagEngine& diag);

}  // namespace delta
