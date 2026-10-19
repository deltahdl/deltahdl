#pragma once

#include "simulator/vpi_object.h"

namespace delta {

// §37.10: answers into `value` the integer and Boolean properties the figure
// draws on every instance and takes from its definition -- vpiCellInstance,
// vpiProtected, vpiDefNetType, vpiUnconnDrive, vpiDefDelayMode and vpiTop --
// a package's vpiUnit and a §37.36 udp defn's vpiProtected, saying whether
// `property` was one of them for `obj`. Answers false for any other, and for
// vpiProtected of an object neither an instance nor a udp defn, which a gen
// scope answers for itself (§37.85).
bool VpiGetInstanceProperty(int property, VpiHandle obj, int& value);

}  // namespace delta
