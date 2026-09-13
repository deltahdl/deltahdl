#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <type_traits>

// Annex H.10.1 says what the include file svdpi.h is: the main include file
// an application using the DPI with C code needs, defining the types for the
// canonical representation of 2-state and 4-state values and for passing
// references to SystemVerilog data objects, providing the function headers,
// and defining helper macros and constants; a file the standard fully
// defines, whose content depends on no implementation or platform, and which
// every simulator shall use as it is. The cases check that the file provides
// each of the four kinds of thing the subclause lists, and that where the
// standard's file (Annex I) fixes a definition this file has it as written --
// the time value struct with its four fields and the three time type codes.
// svdpi.h is included alone: it intentionally redefines a few VPI names, so
// it must not share a translation unit with vpi.h.
#include "simulator/svdpi.h"

namespace delta {
namespace {

// §H.10.1: the types for the canonical representation of 2-state and 4-state
// values -- the scalars svBit and svLogic, and the vector chunks svBitVecVal
// and svLogicVecVal.
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

// §H.10.1: the types for passing references to SystemVerilog data objects --
// a scope and an open array are each handed over as an opaque handle.
TEST(SvdpiIncludeFile, DefinesTheReferencePassingTypes) {
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
}

// §H.10.1: the function headers -- one from each family the file provides,
// referenced so that the declaration must be there.
TEST(SvdpiIncludeFile, ProvidesTheFunctionHeaders) {
  EXPECT_GT(sizeof(&svDpiVersion), 0u);
  EXPECT_GT(sizeof(&svGetBitselBit), 0u);
  EXPECT_GT(sizeof(&svSize), 0u);
  EXPECT_GT(sizeof(&svGetArrElemPtr), 0u);
  EXPECT_GT(sizeof(&svGetScope), 0u);
  EXPECT_GT(sizeof(&svGetTime), 0u);
  EXPECT_GT(sizeof(&svIsDisabledState), 0u);
}

// §H.10.1: the helper macros and constants -- the scalar codes, the chunk
// count and the masking macros.
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

// §H.10.1 with Annex I: the file is the standard's, so the time value type is
// the struct the standard writes -- an int32_t type, uint32_t high and low
// and a double real, in that order -- and the three time type codes are the
// ones the standard's file defines, vpiSuppressTime among them, with the two
// sv_ names standing for the first two.
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
