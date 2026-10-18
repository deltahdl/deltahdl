#pragma once

#include "simulator/vpi_object.h"

namespace delta {

// §37.13 with detail 4: the object whose `relation` an io decl reports in its
// place -- for vpiSize, vpiSigned, vpiScalar and vpiVector, vpiLeftRange,
// vpiRightRange, vpiRange and vpiTypespec, the net or variable it declares,
// reached through the ref obj standing for one passed by reference -- and
// `obj` itself for any other relation, any other object, and an io decl that
// declares none, such as a udp defn's port.
VpiHandle VpiIoDeclStandIn(VpiHandle obj, int relation);

}  // namespace delta
