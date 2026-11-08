#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "simulator/svdpi.h"

namespace delta {
namespace {

TEST(SvdpiIncludeFile, DefinesCanonicalTwoStateRepresentationTypes) {
  svBit bit_value = sv_0;
  EXPECT_EQ(bit_value, 0);
  bit_value = sv_1;
  EXPECT_EQ(bit_value, 1);

  svBitVecVal word = 0xFFFFFFFFu;
  EXPECT_EQ(word, 0xFFFFFFFFu);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);

  EXPECT_TRUE(std::is_unsigned<svBit>::value);
  EXPECT_TRUE(std::is_unsigned<svBitVecVal>::value);
}

TEST(SvdpiIncludeFile, DefinesCanonicalFourStateRepresentationTypes) {
  svLogic logic_value = sv_0;
  EXPECT_EQ(logic_value, 0);
  logic_value = sv_1;
  EXPECT_EQ(logic_value, 1);
  logic_value = sv_z;
  EXPECT_EQ(logic_value, 2);
  logic_value = sv_x;
  EXPECT_EQ(logic_value, 3);

  svLogicVecVal logic_word{};
  logic_word.aval = 0u;
  logic_word.bval = 0u;
  EXPECT_EQ(logic_word.aval, 0u);
  EXPECT_EQ(logic_word.bval, 0u);

  EXPECT_GT(sizeof(svLogicVecVal), sizeof(svBitVecVal));
}

TEST(SvdpiIncludeFile, DefinesReferenceTypesForDataObjects) {
  svScope scope = nullptr;
  svOpenArrayHandle array = nullptr;

  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(array, nullptr);

  EXPECT_TRUE(std::is_pointer<svScope>::value);
  EXPECT_TRUE(std::is_pointer<svOpenArrayHandle>::value);
}

TEST(SvdpiIncludeFile, ProvidesInterfaceFunctionHeaders) {
  const char* (*version)(void) = &svDpiVersion;
  svScope (*get_scope)(void) = &svGetScope;
  svBit (*get_bitsel)(const svBitVecVal*, int) = &svGetBitselBit;
  int (*dimensions)(svOpenArrayHandle) = &svDimensions;

  EXPECT_NE(version, nullptr);
  EXPECT_NE(get_scope, nullptr);
  EXPECT_NE(get_bitsel, nullptr);
  EXPECT_NE(dimensions, nullptr);
}

TEST(SvdpiIncludeFile, DefinesHelperMacrosAndConstants) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);

  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFu, 4), 0xFu);

#if defined(sv_x) && defined(SV_MASK) && defined(SV_GET_UNSIGNED_BITS)
  SUCCEED();
#else
  FAIL() << "svdpi.h must define the helper constants and macros";
#endif
}

TEST(SvdpiIncludeFile, ContentIsImplementationIndependent) {
#ifdef INCLUDED_SVDPI
  SUCCEED();
#else
  FAIL() << "svdpi.h must be a single guarded include file";
#endif

  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svScalar, uint8_t>::value));

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
