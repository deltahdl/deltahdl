#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include "simulator/svdpi.h"

namespace delta {
namespace {

TEST(SvdpiIncludeFile, DefinesTheCanonicalRepresentationTypes) {
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svLogicVecVal, s_vpi_vecval>::value));
  svLogicVecVal chunk{};
  chunk.aval = 1u;
  chunk.bval = 1u;
  EXPECT_EQ(chunk.aval, 1u);
  EXPECT_EQ(chunk.bval, 1u);
}

TEST(SvdpiIncludeFile, DefinesTheReferencePassingTypes) {
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
}

TEST(SvdpiIncludeFile, ProvidesTheFunctionHeaders) {
  EXPECT_GT(sizeof(&svDpiVersion), 0u);
  EXPECT_GT(sizeof(&svGetBitselBit), 0u);
  EXPECT_GT(sizeof(&svSize), 0u);
  EXPECT_GT(sizeof(&svGetArrElemPtr), 0u);
  EXPECT_GT(sizeof(&svGetScope), 0u);
  EXPECT_GT(sizeof(&svGetTime), 0u);
  EXPECT_GT(sizeof(&svIsDisabledState), 0u);
}

TEST(SvdpiIncludeFile, DefinesTheHelperMacrosAndConstants) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(32), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_MASK(3), 0x7u);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFu, 3), 0x7u);
}

TEST(SvdpiIncludeFile, TheTimeValueTypeAndCodesAreTheStandardsOwn) {
  EXPECT_TRUE((std::is_same<svTimeVal, s_vpi_time>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::type), int32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::high), uint32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::low), uint32_t>::value));
  EXPECT_TRUE((std::is_same<decltype(s_vpi_time::real), double>::value));
  EXPECT_LT(offsetof(s_vpi_time, type), offsetof(s_vpi_time, high));
  EXPECT_LT(offsetof(s_vpi_time, high), offsetof(s_vpi_time, low));
  EXPECT_LT(offsetof(s_vpi_time, low), offsetof(s_vpi_time, real));
  EXPECT_EQ(vpiScaledRealTime, 1);
  EXPECT_EQ(vpiSimTime, 2);
  EXPECT_EQ(vpiSuppressTime, 3);
  EXPECT_EQ(sv_scaled_real_time, vpiScaledRealTime);
  EXPECT_EQ(sv_sim_time, vpiSimTime);
}

}  // namespace
}  // namespace delta
