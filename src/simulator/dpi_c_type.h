#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

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

// §H.11.4: an unpacked array formal that is not an open array has the same
// layout a C compiler gives an array of the element's C type with the same
// dimension sizes, and C code reaches its elements by C indexing, which is
// the mapping of §H.7.6: each dimension is counted from 0 in the natural
// order, so the element at SystemVerilog index min(L,R) of a dimension [L:R]
// is at C index 0 and the one at max(L,R) at abs(L-R), the elements lie in
// row-major order with the last dimension varying fastest, and each is
// sizeof the element's C type apart. An open array is what §H.8.6 passes by
// handle instead and is reached through the functions of §H.12.

// The C declaration of such a formal: the element's C type, the formal's
// name and one [size] per unpacked dimension in declaration order, each size
// the count of the dimension's range -- `int a [3:1][2:5]` is `int a[3][4]`.
// A packed element is its canonical array of chunks (§H.7.7), one more
// dimension of ceil(width/32) of them, so `logic [17:0] b [1:10][31:0]` is
// `svLogicVecVal b[10][32][1]`; an input's element is const, as §H.8.7 has
// every input. An empty string is returned for an element type the DPI
// does not pass.
std::string DpiCDeclarationOfUnpackedFormal(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims);

// The size in bytes of one element as C lays it out, sizeof the element's C
// type -- 4 for an int, 8 for a longint, one svBitVecVal or svLogicVecVal per
// 32 bits of a packed element -- which is what one step along the last
// dimension moves the address by. 0 for an element type the DPI does not
// pass.
std::size_t DpiCElementBytes(const DpiArg& formal);

// The C indices of the element at SystemVerilog indices `sv_indices`, one per
// unpacked dimension: sv - min(L,R) for a dimension [L:R], by §H.7.6 c).
std::vector<uint32_t> DpiCIndicesOfUnpackedElement(
    const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices);

// The byte offset of that element from the start of the array under the C
// compiler's layout: the row-major linear index, the last dimension varying
// fastest, times the element's size.
std::size_t DpiCOffsetOfUnpackedElement(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices);

}  // namespace delta
