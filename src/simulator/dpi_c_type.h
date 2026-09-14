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
//     svBitVecVal* or svLogicVecVal*, a small type's T*;
//   - a struct or union named by its type (DpiArg::type_name) is passed by
//     reference to the C-compatible object of that type (§H.7.5, §H.8.4), a
//     const T* for an input and a T* otherwise -- §H.10.2's `pair i2` is
//     `const pair* i2`.
// integer and time are packed 4-state types (§H.7.3) and so cross as
// svLogicVecVal; a reg is a logic (Table H.1). An empty string is returned
// for a kind the DPI does not pass, an unnamed struct or union among them.
std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array);

// §H.8.8: an inout or output argument, open arrays excepted, is always
// passed by reference, a packed array as svBitVecVal* or svLogicVecVal*
// (DpiCTypeOfFormal, DpiPassingModeOfFormal), and the same rules about
// unused bits apply as in §H.7.7: the bits of the last chunk beyond the
// width are undetermined whichever way the value crosses, and the value
// is what lies within the width.
bool DpiOutputOrInoutIsPassedByReference(const DpiArg& formal, bool open_array);

// §H.8.7: an input argument of an imported function implemented in C shall
// always have a const qualifier, which DpiCTypeOfFormal gives every input;
// an input, open arrays apart, is passed by value or by reference depending
// on its size, a small value by value and an input of any other type by
// reference.

// Whether a type is one of the small ones an input of which is passed by
// value.
bool DpiTypeIsSmall(DataTypeKind kind);

// The small types as the clause lists them: byte, shortint, int, longint,
// real and shortreal; scalar bit and logic; chandle and string.
const std::vector<DataTypeKind>& DpiSmallTypes();

// §H.8 defines the ways to pass arguments in the C layer of the DPI, and
// §H.8.1 gives the overview: an argument is generally passed by some form
// of reference, except a small value of an input argument, which is passed
// by value, and the function result, restricted to small values, which is
// passed by value, directly returned. A formal other than an open array is
// passed by direct reference or by value and so is directly accessible in
// C code; an open array formal is passed by handle, an svOpenArrayHandle,
// and reached through the library functions of §H.12.
enum class DpiPassingMode : uint8_t { kByValue, kByReference, kByHandle };

// The mode a formal is passed in: by handle for an open array whatever its
// type or direction, by value for an input of a small type, and by
// reference for the rest -- an output or inout of any type, an input packed
// array.
DpiPassingMode DpiPassingModeOfFormal(const DpiArg& formal, bool open_array);

// The mode a function result is passed in: by value.
DpiPassingMode DpiPassingModeOfResult();

// §H.8.1: whether a mode is a form of reference, which by reference and by
// handle are and by value, the exception a small input alone takes, is
// not.
bool DpiModeIsAFormOfReference(DpiPassingMode mode);

// §H.8.1: whether a type may be a function result, the result being
// restricted to small values: a small type, or void for a function
// returning none.
bool DpiTypeMayBeAResult(DataTypeKind kind);

// §H.8.9: the types a function result is restricted to, as the clause
// lists them: byte, shortint, int, longint, real, shortreal, chandle and
// string, and scalar bit and logic -- each returned as the C type Table
// H.1 gives it (DpiCTypeOfResult), a scalar bit or logic under svdpi.h's
// encoding (§H.10.1.1).
const std::vector<DataTypeKind>& DpiResultTypes();

// §H.8.3: only a small value of a formal input argument is passed by
// value, a function result is directly passed by value as well, and the
// user provides the C type equivalent to the SystemVerilog type of a
// formal passed by value, which DpiCTypeOfFormal spells.

// Whether a formal is passed by value: an input of a small type that is
// not an open array.
bool DpiFormalIsPassedByValue(const DpiArg& formal, bool open_array);

// The C type a function result is returned as: the type Table H.1 maps the
// SystemVerilog type to, unqualified, a scalar bit or logic under its svBit
// or svLogic name, void for no result, and nothing for a type §35.5.5 keeps
// from being a result.
std::string DpiCTypeOfResult(DataTypeKind kind);

// Whether a formal passed in a mode is directly accessible in C: it is by
// value or by reference, and not by handle.
bool DpiFormalIsDirectlyAccessibleInC(DpiPassingMode mode);

// §H.8.6: an argument specified as an open, unsized array is always passed
// by a handle, regardless of the direction of the SystemVerilog formal,
// and is reached through library functions; the implementation of a handle
// is tool specific and transparent to the user, the handle being the
// generic pointer void* under the name svOpenArrayHandle (this simulator's
// pointing at the descriptor of svdpi_open_array.h); and an argument passed
// by handle shall always have a const qualifier, because the user shall
// not modify the contents of a handle.

// The C type every argument passed by handle takes, whatever its direction
// and element type: const svOpenArrayHandle.
std::string_view DpiCTypeOfHandleArgument();

// Whether the user may modify the contents of a handle: never, which the
// const qualifier says.
bool DpiUserMayModifyHandleContents();

// §H.7 defines the data types of the C layer of the DPI, and a value
// crosses the interface as one of them: a basic type of Table H.1 (§H.7.4),
// which the small types of §H.8.7 are, the canonical representation of a
// packed array (§H.7.7), or the handle of an open array (§H.12). A type
// none of them covers does not cross.
enum class DpiCLayerType : uint8_t {
  kBasic,
  kCanonicalElement,
  kOpenArrayHandle,
  kNone
};

// Which of the layer's types a formal crosses as: the handle for an open
// array whatever its type, the canonical representation for a packed
// array, integer and time included, a basic type for a small type, and
// none for the rest.
DpiCLayerType DpiCLayerTypeOfFormal(const DpiArg& formal, bool open_array);

// The subclause of Annex H that defines one of the layer's types; empty for
// kNone.
std::string_view DpiSubclauseDefiningCLayerType(DpiCLayerType type);

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
// every input, which a string's const char* already carries so that an
// array of strings is `const char* s[3]` in every direction (§H.8.10.1).
// An empty string is returned for an element type the DPI does not pass.
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

// §H.7.3: the DPI restricts how SystemVerilog data types are represented
// in C. A type that is not packed and holds no packed element has a
// C-compatible representation; a basic integer or real type is represented
// as §H.7.4 defines; a packed type, time and integer and a user-defined
// packed type among them, in the canonical form of §H.7.7; an enumeration
// by the C type of its SystemVerilog base type, an integer or time base
// being a 4-state packed array, the base type deciding whether the
// enumeration is a small value (§35.5.5) and its names unavailable in C.
// An unpacked array embedded in a struct, and a stand-alone array passed
// to a sized formal, have a C-compatible layout whatever their element; a
// stand-alone array passed to an open array formal is in canonical form
// where its element is a 2-state or 4-state scalar or packed type and C
// compatible otherwise, an element then having the representation of an
// individual value of its type and reached by C indexing. The elements of
// each dimension of an unpacked array lie in their natural order, the
// lower indices first (§H.7.6 c).

// The representations the clause names, and none for a type that does not
// cross.
enum class DpiRepresentation : uint8_t {
  kCCompatible,
  kBasic,
  kCanonical,
  kNone
};

// The representation a formal takes: canonical for a packed type, basic
// for a small type, C compatible for an unpacked struct or union, none for
// the rest.
DpiRepresentation DpiRepresentationOfFormal(const DpiArg& formal);

// The representation an element of a stand-alone array passed to an open
// array formal takes: canonical for a 2-state or 4-state scalar or packed
// type, a scalar bit or logic included whatever its width, and C
// compatible for every other.
DpiRepresentation DpiRepresentationOfOpenArrayElement(DataTypeKind kind);

// Whether an enumeration with the base type is a small value: it is when
// the base is a small type and not a packed one, so an int base makes one
// and an integer, time or packed bit base does not.
bool DpiEnumIsSmall(DataTypeKind base, uint32_t base_width);

// §H.7.8: imported and exported DPI subroutines can take unpacked
// aggregate types -- unpacked arrays and structures -- as formal or actual
// arguments, composed of packed elements, unpacked elements or both,
// subaggregates included, a nonaggregate element being one of the basic
// types of Table H.1 (§35.5.6). Where an unpacked type consists purely of
// unpacked elements, subaggregates included, the layout presented to the C
// programmer is guaranteed to be compatible with the C compiler's layout on
// the operating system; an aggregate may include packed elements as well,
// without that guarantee, each in the canonical form of §H.7.7.

// One element of an unpacked aggregate: a nonaggregate of a basic type,
// packed where the type and width make a packed array, or a subaggregate
// with elements of its own.
struct DpiAggregateElement {
  DataTypeKind kind = DataTypeKind::kInt;
  uint32_t width = 0;
  std::vector<DpiAggregateElement> members;
};

// Whether an aggregate is one the interface takes as an argument: every
// nonaggregate element, down through the subaggregates, a basic type of
// Table H.1 or a packed array of bit or logic.
bool DpiAggregateIsAnArgument(const DpiAggregateElement& aggregate);

// Whether the aggregate's layout is guaranteed to be the C compiler's: it
// is where every element, down through the subaggregates, is unpacked, and
// not where a packed element lies anywhere in it.
bool DpiAggregateLayoutIsCCompatible(const DpiAggregateElement& aggregate);

// §H.8.4: an argument passed by reference is passed as a pointer to the
// actual data object, and packed data as a pointer to a canonical data
// object (§H.7.7); the actual is usually the caller's allocation, or an
// object allocated elsewhere the caller holds a reference to, its own
// formal passed by reference for one. An argument of type T passed by
// reference has a formal of type T*, DpiCTypeOfFormal's spelling, a packed
// array a pointer to the canonical type, svLogicVecVal* or svBitVecVal*. A
// DPI C application shall make no assumption about the lifetime of an
// argument passed by reference: a value to keep across calls is copied
// into memory the C application owns and manages (§H.6.6).

// What the pointer a formal is passed by refers to: the actual data object
// itself, or for packed data a canonical data object.
enum class DpiReferent : uint8_t { kActualDataObject, kCanonicalDataObject };
DpiReferent DpiReferentOfFormal(const DpiArg& formal);

// Whether a reference an argument was passed by may be assumed to remain
// valid once the call has returned: never.
bool DpiReferenceOutlivesTheCall();

// The side owning the copy a C application keeps of a referenced value
// across calls: C.
DpiMemorySide DpiSideOwningACopyKeptAcrossCalls();

// §H.8.2: there is no difference in argument passing between a call from
// SystemVerilog to C and one from C to SystemVerilog. A task or function
// exported from SystemVerilog cannot have an open array as an argument;
// apart from that restriction the same types of formal can be declared for
// an export as for an import, and a subroutine exported from SystemVerilog
// shall have the same function header in C as an imported function with
// the same result type and the same formal list would. For an argument
// passed by reference, the actual to a SystemVerilog subroutine called
// from C shall be allocated with the same layout of data SystemVerilog
// uses for that type, the caller being responsible for the allocation.
// Calling a SystemVerilog task from C is the same as calling a function
// from C, except that the return type of an exported task is an int whose
// meaning §35.9 gives.

// The function header a subroutine has in C: the result's C type, the
// name, and the formals in declaration order each as DpiCTypeOfFormal
// spells it followed by its name, a subroutine with no formals taking ().
std::string DpiCFunctionHeader(std::string_view c_name, DataTypeKind result,
                               const std::vector<DpiArg>& formals);

// The header an exported subroutine has: that of an import with the same
// result and formals, the result being int for a task.
std::string DpiCHeaderOfExportedSubroutine(std::string_view c_name,
                                           DataTypeKind result,
                                           const std::vector<DpiArg>& formals,
                                           bool is_task);

// The C type an exported task returns: int.
std::string_view DpiCTypeOfExportedTaskResult();

// Whether an export's formal may be an open array: never.
bool DpiExportFormalMayBeAnOpenArray();

// Whether an export's formal may have a type: the same types an import's
// may, those the C layer has a type for.
bool DpiExportFormalMayHaveType(DataTypeKind kind);

// The side that allocates an actual passed by reference to a SystemVerilog
// subroutine called from C: the caller, C.
DpiMemorySide DpiSideAllocatingActualOfExportCall();

// §H.8.5: relevant only to calling an exported SystemVerilog subroutine
// from C, where the caller is responsible for allocating every actual
// argument passed by reference. Static allocation requires knowledge of
// the data type; where the type involves SystemVerilog packed arrays, a C
// array of the canonical type, svLogicVecVal or svBitVecVal, is allocated
// and initialized before being passed by reference to the export.

// Whether the caller of an export allocates the actual for a formal: it
// does for one passed by reference, and not for one passed by value.
bool DpiCallerAllocatesExportActual(const DpiArg& formal);

// The C declaration that allocates the actual for a formal: an object of
// Table H.1's type for a small type, and for a packed array a C array of
// its canonical type with one element per 32 bits, `svLogicVecVal w[2]`
// for logic [39:0] -- without the const of an input, which qualifies the
// export's view and not the caller's allocation. Empty for a type the DPI
// does not pass.
std::string DpiCAllocationOfExportActual(const DpiArg& formal);

// §H.8.10: the layout of a SystemVerilog string is implementation
// dependent, but a string passed from SystemVerilog to C is laid out as a
// C string with its trailing null, and a C string passed to SystemVerilog
// is the user's to null-terminate. The direction mode applies to the
// pointer, Table H.1's const char*, and not to the characters. For an
// import: an input arrives through a pointer SystemVerilog provides that C
// shall not free, makes no lifetime assumption about and whose change is
// not propagated back; an output arrives in a const char** with no
// meaningful value, and C writes a valid address there that SystemVerilog
// shall not free; an inout arrives in a const char** holding a valid
// address to storage C shall not free, and C changes the string by writing
// a new address SystemVerilog shall not free, whose contents SystemVerilog
// then copies into its own memory. For an export: an input reaches
// SystemVerilog through a const char* it only reads; an output is a const
// char** with no meaningful initial value into which SystemVerilog writes
// a valid address, C making no lifetime assumption and not freeing it; an
// inout is a const char** holding a pointer to memory the user allocated,
// which SystemVerilog only reads and changes by writing a valid address of
// its own, again not C's to free or rely on -- a string C wants later it
// copies into memory of its own (§H.6.6).

// The pointer a string argument carries, by who provides it and when.
enum class DpiStringPointerProvider : uint8_t {
  kImportInput,
  kImportOutput,
  kImportInoutOnArrival,
  kImportInoutChanged,
  kExportInput,
  kExportOutput,
  kExportInoutOnArrival,
  kExportInoutChanged,
};

// The side that provided the pointer, whose storage the string is and who
// alone may free it (DpiSideMayFree): SystemVerilog for what it hands C
// and C for what it hands SystemVerilog.
DpiMemorySide DpiSideProvidingStringPointer(DpiStringPointerProvider provider);

// The side that copies the string a pointer refers to when it is to be
// kept: the receiving side, which makes no assumption about the storage's
// lifetime.
DpiMemorySide DpiSideCopyingString(DpiStringPointerProvider provider);

// Whether the side receiving a string may modify its characters: never.
bool DpiStringCharactersMayBeModifiedByReceiver();

// §H.8.10.1: a string contained in an aggregate argument is represented
// by a const char* member too, and every stipulation of §H.8.10 on a
// stand-alone string applies to it as well. An array of strings takes no
// extra level of indirection, the one a stand-alone output or inout has:
// by §H.7.8 every array of strings is represented in C as const char**,
// whatever its direction.

// The C type of a string member of an aggregate: Table H.1's const char*.
std::string_view DpiCTypeOfStringMember();

// Whether the stipulations on a string member of an aggregate are those on
// a stand-alone string argument -- who provides its pointer, who may free
// its storage, who copies it and that its characters are not modified:
// always.
bool DpiStringMemberStipulationsAreStandalone();

// The C type of an array of strings in the direction: const char** for an
// input, an output and an inout alike, the element const char* with the
// array's own indirection and no other.
std::string_view DpiCTypeOfStringArray(Direction direction);

// §H.11: normalized ranges are used for accessing SystemVerilog arrays,
// with the exception of formal arguments specified as open arrays. A sized
// packed or unpacked dimension [L:R] is accessed in C as [size-1:0], so an
// index counts from the low bound (DpiCIndicesOfUnpackedElement,
// DpiNormalizedBitIndex); an open array keeps the ranges of the actual bound
// to it, which the querying functions of §H.12.2 report and by which its
// elements are indexed in C as in SystemVerilog (§H.12).
enum class DpiArrayRanges : uint8_t { kNormalized, kOfTheActual };

DpiArrayRanges DpiRangesUsedForAccessing(bool formal_is_open_array);

// The normalized range of a dimension declared [L:R]: [size-1:0].
SvActualDimension DpiNormalizedRange(SvActualDimension declared);

// The ranges an array's dimensions are accessed by: each normalized for a
// sized formal, and the declared ranges of the actual as they are for an
// open array formal.
std::vector<SvActualDimension> DpiRangesForAccessing(
    const std::vector<SvActualDimension>& declared, bool formal_is_open_array);

// §H.11.2: multiple packed dimensions of a SystemVerilog array are
// linearized (§H.7.5) into the one normalized packed dimension the C side
// sees, [size-1:0] with size the product of the dimensions' counts, so that
// `bit [6:1][1:8]` is [47:0] in two canonical chunks; unpacked arrays can
// have an arbitrary number of dimensions, each a dimension of the C array.
SvActualDimension DpiLinearizedPackedRange(
    const std::vector<SvActualDimension>& packed_dims);

// The number of packed dimensions the C side sees of a packed array: one.
uint32_t DpiPackedDimensionCountInC();

// Whether the number of unpacked dimensions is limited: never.
bool DpiUnpackedDimensionCountIsLimited();

// §H.12.3: the access functions of the C layer are of two families: the
// library functions for copying data between an open array handle and a
// canonical form buffer the C programmer provides (§H.12.5), and the
// functions for obtaining the actual address of a SystemVerilog data object
// or of an individual element of an unpacked array (§H.12.4).
enum class DpiOpenArrayAccess : uint8_t {
  kCopyElementToCanonicalBuffer,
  kCopyElementFromCanonicalBuffer,
  kAddressOfArray,
  kAddressOfElement,
};

// The side providing the canonical form buffer a copy goes to or from: C.
DpiMemorySide DpiSideProvidingCanonicalBuffer();

// Whether an access copies through a canonical buffer or yields an address.
bool DpiAccessCopiesThroughCanonicalBuffer(DpiOpenArrayAccess access);

// The library function of svdpi.h that performs an access, for an element
// of type bit where `four_state` is false and of type logic where true; the
// address functions serve either type.
std::string_view DpiAccessFunction(DpiOpenArrayAccess access, bool four_state);

// §H.11.3: a packed struct or union argument corresponds to a
// one-dimensional packed array argument of its width, of type bit where its
// members are 2-state and logic where 4-state -- the formal DpiCTypeOfFormal
// spells and the canonical representation of §H.7.7 applies to, so that the
// example's A, S and U formals are each a const svBitVecVal* holding the
// three bits, whichever of the three types declared them.
DpiArg DpiPackedAggregateAsPackedArrayFormal(const DpiArg& aggregate,
                                             bool four_state, uint32_t width);

// §H.11.1: two alternatives for working with 2-state packed data. A DPI
// formal argument can be of a C-compatible type -- the classical int-to-int
// correspondence of Table H.1, or an int unsigned an arbitrary 2-state bit
// vector actual is associated with by the caller's coercion (§H.6) -- or a
// packed formal of the vector's width, passed as the canonical const
// svBitVecVal* of §H.7.7, the portable technique for an arbitrary width.
// The canonical technique is less efficient than a C-compatible formal, and
// required once a 2-state vector exceeds 64 bits.
enum class DpiTwoStateTechnique : uint8_t { kCCompatibleFormal, kCanonical };

// Whether a 2-state vector of the width can be handled by a C-compatible
// formal: it can up to 64 bits, beyond which the canonical technique is
// required.
bool DpiCCompatibleFormalCanHoldTwoStateVector(uint32_t width);

// The technique required for a 2-state vector of the width: the canonical
// one beyond 64 bits, either up to it -- the C-compatible one, being the
// more efficient, where the choice is open.
DpiTwoStateTechnique DpiTechniqueRequiredForTwoStateVector(uint32_t width);

// Whether one technique is more efficient than the other: a C-compatible
// formal is more efficient than the canonical technique.
bool DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique technique,
                                 DpiTwoStateTechnique other);

// §H.10.3 with §H.7.8 and §H.11: a packed array member of an unpacked
// aggregate is declared in the C-compatible struct as an inout formal of
// its type would be, no direction qualifying it, in the normalized ranges
// of §H.11 -- the example's `bit [6:1][1:8] b [65:2]` is defined as for
// `bit [47:0] b [63:0]`, svBitVecVal b[64][2], two chunks holding the
// linearized 48 packed bits (SV_PACKED_DATA_NELEMS(6*8)). The packed
// dimensions are given as declared and linearized here; a member of a small
// type has no packed dimensions and no chunk dimension.
std::string DpiCDeclarationOfAggregateMember(
    std::string_view name, DataTypeKind kind,
    const std::vector<SvActualDimension>& packed_dims,
    const std::vector<SvActualDimension>& unpacked_dims);

// §H.10: the C layer of the DPI defines one include file, svdpi.h. The file
// is implementation independent and defines the canonical representation,
// all basic types and all interface functions; the actual file is shown in
// Annex I, and this simulator's src/simulator/svdpi.h is that file.
std::string_view DpiCLayerIncludeFile();
uint32_t DpiCLayerIncludeFileCount();
bool DpiCLayerIncludeFileIsImplementationIndependent();

// §H.10: what the include file defines.
enum class DpiIncludeFileContent : uint8_t {
  kCanonicalRepresentation,
  kBasicTypes,
  kInterfaceFunctions,
};

bool DpiIncludeFileDefines(DpiIncludeFileContent content);

// §H.10: where the standard shows the actual file.
std::string_view DpiAnnexShowingIncludeFile();

}  // namespace delta
