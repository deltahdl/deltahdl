#pragma once

#include <string>

#include "simulator/dpi_arg_value.h"

namespace delta {

// §H.7.2: a value crossing the DPI is a value of a SystemVerilog type on one
// side and of a C type on the other, so each type passed through the
// interface needs two matching definitions, and for each SystemVerilog type
// an import or export declaration uses, the user shall provide the equivalent
// C type definition, one reflecting the argument passing mode for that type
// (§H.8) and the direction of the formal. This is the C definition matching
// a formal, spelled as it stands in the C prototype:
//   - an open array, whatever its direction, is passed by handle (§H.8.6), a
//     const svOpenArrayHandle;
//   - an input of a small type (§H.8.7: byte, shortint, int, longint, real,
//     shortreal, a scalar bit or logic, chandle and string) is passed by
//     value as the C type Table H.1 maps it to, with the const qualifier
//     every input carries;
//   - an input of any other type is passed by reference to its canonical
//     representation, a const svBitVecVal* or const svLogicVecVal* (§H.8.4);
//   - an inout or output, open arrays apart, is always passed by reference
//     (§H.8.8), a pointer to the C type of the value -- a packed array's
//     svBitVecVal* or svLogicVecVal*, a small type's T*.
// integer and time are packed 4-state types (§H.7.3) and so cross as
// svLogicVecVal; a reg is a logic (Table H.1). An empty string is returned
// for a kind the DPI does not pass.
std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array);

// §H.8.7: whether a type is one of the small ones an input of which is
// passed by value.
bool DpiTypeIsSmall(DataTypeKind kind);

}  // namespace delta
