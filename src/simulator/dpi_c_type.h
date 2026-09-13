#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/svdpi_open_array.h"

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

// §H.7.4: Table H.1's mapping of the basic SystemVerilog data types to C
// types -- byte to char, shortint to short int, int to int, longint to long
// long, real to double, shortreal to float, chandle to void*, string to
// const char*, and bit and logic to unsigned char under the encodings
// svdpi.h gives them, reg using logic's -- and, with `is_unsigned`, the
// unsigned integer types the DPI also supports, each mapped to the unsigned
// C type corresponding to its signed equivalent's row: unsigned char,
// unsigned short, unsigned int and unsigned long long. The qualifier changes
// nothing for a type with no signed row. Empty for a type the table has no
// row for. Since byte unsigned crosses as unsigned char by value and bit
// [7:0] as svBitVecVal by reference, and likewise shortint unsigned and bit
// [15:0], the one is not equivalent to the other in any direction, which
// DpiCTypeOfFormal reflects.
std::string DpiCTypeOfBasicType(DataTypeKind kind, bool is_unsigned);

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

// §H.12: a formal declared as an open array takes actuals of different
// sizes -- a different range, a different count of elements -- so C code
// written against it handles SystemVerilog arrays of any size; its elements
// are reached in C by the same range of indices and the same indexing as in
// SystemVerilog, and the dimensions and original bounds of the actual can
// be inquired about (§H.12.2). The sole packed dimension (§H.7.1) and any
// number of unpacked dimensions can be unsized (§35.5.6.1). Every open array
// formal is passed by handle, an svOpenArrayHandle, whatever its direction
// (DpiCTypeOfFormal above), and is reached through the functions that take
// the handle, svGetArrayPtr among them giving its address. For an inout or
// output open array the space C code may write is determined by the
// actual's size, and writing more to the array's address than the actual's
// capacity accommodates is undefined. The handle's descriptor
// (svdpi_open_array.h) records what the actual bound on the call: its
// dimension 0 is the packed part and dimensions 1 and up the unpacked ones.

// The count of elements the actual has: the product of the sizes of its
// unpacked dimensions, 1 where the array is a packed vector alone and 0 for
// a descriptor recording no dimensions, which describes no actual.
uint64_t DpiOpenArrayElementCount(const SvOpenArrayDesc& desc);

// The capacity of an inout or output open array in bytes, the space C code
// may write: the element count times the byte stride of an element the
// descriptor records, 0 where that stride is 0 because the element's
// representation differs from a value's (§H.12.4) and there is no address
// to write at.
uint64_t DpiOpenArrayCapacityBytes(const SvOpenArrayDesc& desc);

// Whether a write of `bytes` from the array's address is one §H.12 defines:
// no more than the capacity.
bool DpiOpenArrayWriteIsDefined(const SvOpenArrayDesc& desc, uint64_t bytes);

// §H.7.7: the DPI defines a canonical representation for packed arrays, of
// type svBitVecVal for a 2-state array and svLogicVecVal for a 4-state one,
// the latter fully equivalent to the s_vpi_vecval the VPI represents 4-state
// logic in. A packed array is represented as an array of one or more
// elements, each a group of 32 bits: the first holds the 32 least
// significant bits, the next the 32 more significant, and so on. The last
// element can hold unused bits, whose contents are undetermined, and the
// user is responsible for masking them or, by the sign, for sign extension
// over them.

// The bits one element of the representation groups.
constexpr uint32_t kDpiCanonicalElementBits = 32;

// The C type of one element of the canonical representation of a packed
// array of a type: svBitVecVal for bit, svLogicVecVal for logic and reg and
// for integer and time, packed 4-state by §H.7.3; empty for a type with no
// canonical representation.
std::string DpiCanonicalElementType(DataTypeKind kind);

// Where a bit of a packed array lies in the representation, the bit given
// by its normalized index (§H.7.6 b): the element holding it, and the bit
// within that element.
struct DpiCanonicalBitPosition {
  uint32_t element = 0;
  uint32_t bit = 0;
};
DpiCanonicalBitPosition DpiCanonicalPositionOfBit(uint32_t bit);

// The count of unused bits in the last element of the representation of a
// `width`-bit array: 32 less the bits the last group holds, none when the
// width is a multiple of 32. DpiCanonicalWordCount in dpi_arg_value.h is
// how many elements there are.
uint32_t DpiCanonicalUnusedBits(uint32_t width);

// The last element `last` of a `width`-bit array with its unused bits given
// the contents the user is responsible for: cleared for an unsigned array,
// or each set to the array's sign, its most significant bit, for a signed
// one; unchanged when the element has no unused bits.
uint32_t DpiCanonicalLastElementWithUnusedBits(uint32_t last, uint32_t width,
                                               bool is_signed);

// §H.6, restating §35.5.1: the formal and actual arguments of imported and
// exported subroutines are bound by the WYSIWYG principle -- the callee gets
// its actuals as specified for its formals, and the caller's arguments
// conform to the formal types, by coercion on the caller's side where
// necessary. No compiler on either side can coerce between the caller's
// declared formals and the callee's, the two being declared in different
// languages with no visible relationship between them, so the user provides
// matched types on both sides (§H.7.2), the imported or exported function's
// types matching those of the corresponding foreign subroutine, a qualifier
// such as rand ignored. What the SystemVerilog compiler does provide is the
// coercion of the actual arguments of every imported call to the formal's
// type, truncating or extending the bits of a packed array whose width
// differs from the formal's.

// The coercion the caller's side gives a packed actual of one width bound
// to a formal of another.
enum class DpiActualCoercion : uint8_t { kNone, kTruncate, kExtend };
DpiActualCoercion DpiCoercionOfPackedActual(uint32_t actual_width,
                                            uint32_t formal_width);

// Whether the type a C prototype declares for a formal is the one
// DpiCTypeOfFormal says the SystemVerilog declaration requires, the spacing
// around a * being no part of it.
bool DpiCTypeMatchesFormal(const DpiArg& formal, bool open_array,
                           std::string_view c_type);

}  // namespace delta
