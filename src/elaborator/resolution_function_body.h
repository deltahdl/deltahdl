#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleItem;

// §6.6.7 (printed page 98): a resolution function shall not resize its dynamic
// array argument or write any part of it, and shall have no side effects, since
// the simulator calls it as often as driver updates happen to arrive. Reports
// each statement of the body of `fn` that writes or resizes the driver array,
// and each that writes a variable `fn` does not declare.
void CheckResolutionFunctionBody(const ModuleItem* fn, DiagEngine& diag);

}  // namespace delta
