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

// §H.11.5: a packed array is accessible through its canonical representation
// (§H.7.7), and the C layer's utility functions -- the bit-select and
// part-select functions svdpi.h declares -- work on that representation. A
// part-select is a slice of a packed array of type bit or logic, and there
// is no slice of an unpacked array. The part-select functions reach only a
// narrow subrange of up to 32 bits, and where the range a part-select names
// does not lie wholly within the array's normalized range its behavior is
// undetermined. Source and destination alike are indexed over the
// normalized range [n-1:0] of §H.7.6 b), 0 the LSB.

// Whether a formal is one the bit-select and part-select utilities reach: a
// packed array of bit, logic or reg (a logic by Table H.1), or an integer or
// time since §H.7.3 has them packed 4-state. Not a scalar bit or logic,
// which §H.8.7 passes by value rather than in canonical form, not a type
// with no canonical form, and not an unpacked array as such -- its packed
// elements are, one at a time.
bool DpiPartSelectAppliesTo(const DpiArg& formal);

// The limit §H.11.5 puts on the width of a part-select.
constexpr int kDpiPartSelectMaxWidth = 32;

// Whether a part-select of width `w` starting at normalized index `i` of a
// packed array of `width` bits is one whose behavior §H.11.5 determines:
// the width at least one bit and within the limit, and the bits [(i+w-1):i]
// all within [width-1:0].
bool DpiPartSelectIsDetermined(uint32_t width, int i, int w);

// The normalized index the utilities take for the bit SystemVerilog index
// `sv_index` names in a packed dimension [L:R]: abs(sv_index - R) by §H.7.6
// b), the LSB at R being index 0 and the MSB at L abs(L-R) whichever way
// the range runs, so a[7] of `bit [4:7] a` is index 0 and a[4] index 3.
int DpiNormalizedBitIndex(SvActualDimension packed, int32_t sv_index);

}  // namespace delta
