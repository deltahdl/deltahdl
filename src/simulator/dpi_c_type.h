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

// §H.6.1: the WYSIWYG principle verifies the types of the formal arguments
// of imported functions -- an actual is required to be of the type the
// import declaration specifies for the formal -- with the exception of open
// arrays, whose unspecified ranges are statically unknown. A formal other
// than an open array is fully defined by the declaration: its packed and
// unpacked ranges are exactly as specified there, and only the declaration
// site is relevant to it. An open array formal is passed by handle (§H.12);
// its unpacked dimensions match those of the actual, its packed dimension
// is the linearized, normalized version of all the actual's packed
// dimensions (§H.7.1), and its unsized ranges are determined at each call
// site while the rest of its type is specified at the declaration. So `bit
// [15:8] b []` is an unpacked array of packed bit arrays with bounds 15 to
// 8, and the actual at each call defines the bounds of the unpacked part.

// One dimension of a formal as the import declaration wrote it: sized, with
// the range the declaration gave it, or unsized, which only an open array's
// dimension is.
struct DpiFormalDimension {
  bool sized = true;
  SvActualDimension range;
};

// The ranges a formal has on one call, in the order the descriptor of
// svdpi_open_array.h keeps them for §H.12.2's functions: dimension 0 the
// packed part, then the unpacked dimensions in declaration order, each
// beside the actual's corresponding dimension. A sized dimension keeps the
// declaration's range whatever the actual's; an unsized unpacked dimension
// takes the range of the corresponding actual dimension; an unsized packed
// dimension takes [size-1:0] where size is the product of the sizes of all
// the actual's packed dimensions.
std::vector<SvActualDimension> DpiFormalRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked);

// §H.6.2: a formal specified in SystemVerilog as input shall not be
// modified by the foreign language code (§35.5.1.2). In the C layer the
// const qualifier every input's C type carries (DpiCTypeOfFormal) says so,
// whether the input is passed by value, by reference to its canonical form
// or by handle, and the runtime discards whatever the foreign code wrote to
// an input's copy.

// Whether the foreign code may modify a formal of a direction: an output
// or an inout, never an input.
bool DpiForeignCodeMayModifyFormal(Direction direction);

// §H.6.3: the initial value of a formal specified in SystemVerilog as
// output is undetermined and implementation dependent (§35.5.1.2), so the
// foreign code finds a value it may rely on in an input or an inout, the
// actual's, and none in an output; DpiRuntime::UndeterminedOutputValue is
// what this implementation hands it there.
bool DpiFormalIsDeterminedOnEntry(Direction direction);

// §H.6.4: the SystemVerilog simulator is responsible for handling value
// changes for output and inout arguments, and such changes shall be
// detected and handled after control returns from C code to SystemVerilog
// code -- DpiRuntime::CallImportDetectingChanges is where this simulator
// does so, once the import has returned. This is which directions it
// watches for a change: an output and an inout, and not an input, which
// the foreign code may not modify (§H.6.2).
bool DpiSimulatorDetectsChangesOf(Direction direction);

// §H.6.5, beside §35.5.3: some imported subroutines, or interface functions
// they call, need the context of their call known, which takes special
// instrumentation of their call instances, and to spare the overhead an
// import's calls are instrumented only where the import is declared
// context. An export called from an import has the context the import set
// with svSetScope or otherwise the instantiated scope where the import
// declaration is, DpiRuntime's scope being that context. A noncontext
// import shall not access any SystemVerilog data object other than its
// actual arguments, so its call is no barrier to compiler optimizations,
// where a context import can access any data object through the VPI or an
// embedded export and its call is such a barrier. Only a context import's
// calls are properly instrumented, so only it can safely call functions of
// other APIs, the VPI and exported subroutines included; from a noncontext
// import the effect is unpredictable, and DpiRuntime refuses it an export
// call. The utility functions of §H.9, svGetScope among them, are what an
// import retrieves and operates on its context with.

// What an import may access of SystemVerilog: its actual arguments alone,
// or any data object.
enum class DpiImportAccess : uint8_t { kActualArgumentsOnly, kAnyDataObject };
DpiImportAccess DpiAccessOfImport(bool is_context);

// Whether an import may safely call functions of other APIs.
bool DpiImportMaySafelyCallOtherApis(bool is_context);

// Whether a call of an import is a barrier to compiler optimizations, which
// DpiRuntime::IsImportCallOptimizationBarrier answers for a registered one.
bool DpiImportCallIsOptimizationBarrier(bool is_context);

// §H.6.6, beside §35.5.1.4: the memory spaces C code and SystemVerilog
// code own and allocate are disjoint, and each side is responsible for its
// own -- C shall not free memory SystemVerilog or its compiler allocated,
// nor expect SystemVerilog to free memory C or its compiler allocated. This
// does not exclude C allocating a block and passing a handle to it to
// SystemVerilog, which in turn calls a C function that frees the block,
// directly if it is free itself or indirectly: in that scenario the block
// is allocated and freed in C even where malloc and free are called
// directly from SystemVerilog code.

// The two sides that own memory.
enum class DpiMemorySide : uint8_t { kC, kSystemVerilog };

// Whether a side may free a block: only the side that allocated it.
bool DpiSideMayFree(DpiMemorySide allocated_by, DpiMemorySide freed_by);

// The side a block a chandle refers to belongs to: C, SystemVerilog holding
// the handle and never the block (§35.5.6 has chandle as the type of such a
// handle).
DpiMemorySide DpiSideOwningBlockBehindChandle();

// The side on which a call of an imported function does its work, free
// among them, whatever SystemVerilog code made the call: C.
DpiMemorySide DpiSideOfImportedCall();

}  // namespace delta
