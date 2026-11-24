#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

#include "simulator/svdpi.h"

namespace {

TEST(SvdpiSourceCode, TheFileIsGuardedByIncludedSvdpi) {
#ifdef INCLUDED_SVDPI
  const bool kGuarded = true;
#else
  const bool kGuarded = false;
#endif
  EXPECT_TRUE(kGuarded);
}

TEST(SvdpiSourceCode, TheLinkageMacrosEndAsTheListingHasThem) {
#if defined(DPI_DLLISPEC) && defined(DPI_DLLESPEC)
  const bool kSpecsDefined = true;
#else
  const bool kSpecsDefined = false;
#endif
  EXPECT_TRUE(kSpecsDefined);
#if defined(DPI_EXTERN) || defined(DPI_PROTOTYPES) || defined(XXTERN) || \
    defined(EETERN)
  const bool kAnySurvives = true;
#else
  const bool kAnySurvives = false;
#endif
  EXPECT_FALSE(kAnySurvives);
}

TEST(SvdpiSourceCode, TheScalarAndChunkTypesAreTheListings) {
  EXPECT_TRUE((std::is_same<svScalar, uint8_t>::value));
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svLogicVecVal, s_vpi_vecval>::value));
  EXPECT_TRUE((std::is_same<p_vpi_vecval, s_vpi_vecval*>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_vecval::aval), uint32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_vecval::bval), uint32_t>::value));
#ifdef VPI_VECVAL
  const bool kVecvalGuarded = true;
#else
  const bool kVecvalGuarded = false;
#endif
  EXPECT_TRUE(kVecvalGuarded);
}

TEST(SvdpiSourceCode, TheTimeValueAndItsCodesAreTheListings) {
  EXPECT_TRUE((std::is_same<svTimeVal, s_vpi_time>::value));
  EXPECT_TRUE((std::is_same<p_vpi_time, s_vpi_time*>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::type), int32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::high), uint32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::low), uint32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::real), double>::value));
  EXPECT_EQ(vpiScaledRealTime, 1);
  EXPECT_EQ(vpiSimTime, 2);
  EXPECT_EQ(vpiSuppressTime, 3);
  EXPECT_EQ(sv_scaled_real_time, vpiScaledRealTime);
  EXPECT_EQ(sv_sim_time, vpiSimTime);
#ifdef VPI_TIME
  const bool kTimeGuarded = true;
#else
  const bool kTimeGuarded = false;
#endif
  EXPECT_TRUE(kTimeGuarded);
}

TEST(SvdpiSourceCode, TheMaskMacroIsTheListingsSignedOne) {
  EXPECT_TRUE((std::is_same<decltype(SV_MASK(4)), int>::value));
  EXPECT_EQ(SV_MASK(0), 0);
  EXPECT_EQ(SV_MASK(4), 0xF);
  EXPECT_EQ(SV_MASK(31), 0x7FFFFFFF);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFFu, 31), 0x7FFFFFFFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFFu, 32), 0xFFFFFFFFu);
  int sign_bit_set = 0x10;
  int sign_bit_clear = 0x0F;
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(sign_bit_set, 4)),
            0xFFFFFFF0u);
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(sign_bit_clear, 4)),
            0x0000000Fu);
}

TEST(SvdpiSourceCode, TheHandlesAndTheVersionRoutineAreTheListings) {
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  EXPECT_TRUE((std::is_same<decltype(svDpiVersion()), const char*>::value));
  EXPECT_STREQ(svDpiVersion(), "1800-2005");
}

TEST(SvdpiSourceCode, TheTimeFunctionsRefuseAHandleThatNamesNoScope) {
  static int not_a_scope = 0;
  auto invalid = reinterpret_cast<svScope>(&not_a_scope);
  svTimeVal time = {};
  time.type = sv_sim_time;
  time.low = 12345;
  int32_t unit = 99;
  int32_t precision = 99;

  EXPECT_EQ(svGetTime(invalid, &time), -1);
  EXPECT_EQ(time.low, 12345u);
  EXPECT_EQ(svGetTimeUnit(invalid, &unit), -1);
  EXPECT_EQ(unit, 99);
  EXPECT_EQ(svGetTimePrecision(invalid, &precision), -1);
  EXPECT_EQ(precision, 99);
  EXPECT_EQ(svGetTimeUnit(nullptr, &unit), 0);
}

}  // namespace
