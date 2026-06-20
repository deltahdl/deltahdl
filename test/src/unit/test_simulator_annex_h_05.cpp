#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

// Annex H.5 names the role of svdpi.h: it is the one main include file of the
// DPI C layer. The clause states what that file must supply -- the types for
// the canonical representation of 2-state (bit) and 4-state (logic) values, the
// types used to pass references to SystemVerilog data objects, the function
// headers of the interface, and a number of helper macros and constants -- and
// that its content does not depend on any particular implementation, so all
// simulators use the same file. These tests include the production header
// directly and observe that it actually carries each of those categories. The
// concern here is the *composition* of the include file (does it define the
// canonical representation, the references, the headers, the helpers), which is
// distinct from H.3's naming spellings and H.4's binary layout. svdpi.h is
// included alone: it intentionally redefines a few VPI names, so it must not
// share a translation unit with vpi.h.
#include "simulator/svdpi.h"

namespace delta {
namespace {

// §H.5: svdpi.h defines the types for the canonical representation of 2-state
// (bit) values. The scalar bit type carries a single Boolean code, and the
// vector word is the canonical packed unit several of which represent a wider
// 2-state value; the element-count helper relates a bit width to that word.
TEST(SvdpiIncludeFile, DefinesCanonicalTwoStateRepresentationTypes) {
  svBit bit_value = sv_0;
  EXPECT_EQ(bit_value, 0);
  bit_value = sv_1;
  EXPECT_EQ(bit_value, 1);

  // The packed 2-state word is the canonical unit; the file states the count of
  // such words needed for a given bit width through its helper.
  svBitVecVal word = 0xFFFFFFFFu;
  EXPECT_EQ(word, 0xFFFFFFFFu);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);

  // The canonical 2-state representation is an unsigned integer encoding.
  EXPECT_TRUE(std::is_unsigned<svBit>::value);
  EXPECT_TRUE(std::is_unsigned<svBitVecVal>::value);
}

// §H.5: svdpi.h defines the types for the canonical representation of 4-state
// (logic) values. The scalar logic type carries all four state codes, and the
// vector word pairs two component fields (the canonical aval/bval encoding) so
// that the z and x states a 2-state word cannot express are representable.
TEST(SvdpiIncludeFile, DefinesCanonicalFourStateRepresentationTypes) {
  svLogic logic_value = sv_0;
  EXPECT_EQ(logic_value, 0);
  logic_value = sv_1;
  EXPECT_EQ(logic_value, 1);
  logic_value = sv_z;
  EXPECT_EQ(logic_value, 2);
  logic_value = sv_x;
  EXPECT_EQ(logic_value, 3);

  // The canonical 4-state word carries the two-component (aval/bval) encoding,
  // which is what lets it represent the z and x states the 2-state word cannot.
  svLogicVecVal logic_word{};
  logic_word.aval = 0u;
  logic_word.bval = 0u;
  EXPECT_EQ(logic_word.aval, 0u);
  EXPECT_EQ(logic_word.bval, 0u);

  // The 4-state word is a strictly richer representation than the 2-state word:
  // it carries the extra component the canonical encoding requires.
  EXPECT_GT(sizeof(svLogicVecVal), sizeof(svBitVecVal));
}

// §H.5: svdpi.h defines the types used to pass references to SystemVerilog data
// objects. Scopes and open arrays are passed across the boundary as such
// reference types rather than by value, and a null reference is a valid value.
TEST(SvdpiIncludeFile, DefinesReferenceTypesForDataObjects) {
  svScope scope = nullptr;
  svOpenArrayHandle array = nullptr;

  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(array, nullptr);

  // A reference to a data object is a handle, i.e., a pointer-like type, not a
  // by-value aggregate.
  EXPECT_TRUE(std::is_pointer<svScope>::value);
  EXPECT_TRUE(std::is_pointer<svOpenArrayHandle>::value);
}

// §H.5: svdpi.h provides the function headers of the interface. Referencing the
// declarations forces svdpi.h to have supplied a prototype with each signature;
// the file would not compile this translation unit otherwise. A representative
// header is taken from each functional group of the interface.
TEST(SvdpiIncludeFile, ProvidesInterfaceFunctionHeaders) {
  // Version, scope access, bit-select access, and array querying each
  // contribute at least one declared header.
  const char* (*version)(void) = &svDpiVersion;
  svScope (*get_scope)(void) = &svGetScope;
  svBit (*get_bitsel)(const svBitVecVal*, int) = &svGetBitselBit;
  int (*dimensions)(svOpenArrayHandle) = &svDimensions;

  EXPECT_NE(version, nullptr);
  EXPECT_NE(get_scope, nullptr);
  EXPECT_NE(get_bitsel, nullptr);
  EXPECT_NE(dimensions, nullptr);
}

// §H.5: svdpi.h defines a number of helper macros and constants. The symbolic
// scalar-state constants and the bit-manipulation helper macros are both part
// of that supplied set; each is exercised so the file must define it.
TEST(SvdpiIncludeFile, DefinesHelperMacrosAndConstants) {
  // Constants: the four scalar-state codes are distinct named values.
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);

  // Helper macros: width/word arithmetic and bit extraction.
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFu, 4), 0xFu);

  // Their presence is testable as preprocessor definitions, confirming the file
  // supplies them as macros rather than as ordinary symbols.
#if defined(sv_x) && defined(SV_MASK) && defined(SV_GET_UNSIGNED_BITS)
  SUCCEED();
#else
  FAIL() << "svdpi.h must define the helper constants and macros";
#endif
}

// §H.5: the content of svdpi.h does not depend on any particular
// implementation, so all simulators shall use the same file. This is observable
// in three ways: the file is a single guarded unit (re-inclusion is idempotent,
// so there is one canonical file); its canonical content is available with no
// implementation- or vendor-selection macro defined by the consumer; and the
// canonical representation types resolve to fixed-width standard integer types,
// giving every consumer the same representation regardless of which simulator
// built against the header.
TEST(SvdpiIncludeFile, ContentIsImplementationIndependent) {
  // One canonical, guarded file: the include guard is set after inclusion, and
  // re-including is a no-op (the guard prevents a second, divergent
  // definition).
#ifdef INCLUDED_SVDPI
  SUCCEED();
#else
  FAIL() << "svdpi.h must be a single guarded include file";
#endif

  // The canonical representation rests on exact-width standard integer types,
  // not implementation-chosen ones, so the same file yields the same
  // representation for every simulator.
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svScalar, uint8_t>::value));

  // The whole set of categories the clause requires is available from this one
  // inclusion with no vendor macro defined: representation types, references,
  // headers, and helpers all resolve together.
  svBit bit_value = sv_1;
  svLogic logic_value = sv_x;
  svScope scope = nullptr;
  (void)bit_value;
  (void)logic_value;
  (void)scope;
  EXPECT_EQ(SV_MASK(3), 0x7u);
}

}  // namespace
}  // namespace delta
