#pragma once

#include "simulator/vpi_object.h"

namespace delta {

// §37.16 detail 23, §37.17 detail 27, §37.19 detail 1, §37.58 detail 3 and
// §37.59 detail 9: the Boolean vpiConstantSelect of `obj`, each clause's rule
// answering for its own kind of object, and 0 for any other kind.
int VpiGetConstantSelect(VpiHandle obj);

}  // namespace delta
