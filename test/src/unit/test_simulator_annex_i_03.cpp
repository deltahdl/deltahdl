#include <gtest/gtest.h>

#include <cstdint>
#include <type_traits>

// svdpi.h is included alone, as every case exercising it does: it redefines
// VPI names vpi.h spells otherwise.
#include "simulator/svdpi.h"

namespace {

// Annex I.3 lists the source code of svdpi.h, and this file is that source:
// the cases below observe the listing's structure in it -- its guard, its
// linkage macros and what becomes of them at the file's end, the types its
// canonical representation and time value are built on and the constants
// that go with them -- beside the names test_simulator_annex_h_03.cpp counts
// and the contents test_simulator_annex_h_10_01.cpp reads.

// §I.3: the file is guarded by INCLUDED_SVDPI.
TEST(SvdpiSourceCode, TheFileIsGuardedByIncludedSvdpi) {
#ifdef INCLUDED_SVDPI
  const bool kGuarded = true;
#else
  const bool kGuarded = false;
#endif
  EXPECT_TRUE(kGuarded);
}

// §I.3: the file defines DPI_DLLISPEC and DPI_DLLESPEC for importing and
// exporting a symbol from a DLL, empty on every platform but Windows, and
// leaves the two defined; DPI_EXTERN, DPI_PROTOTYPES, XXTERN and EETERN it
// undefines at its end, so that none of the four survives the inclusion.
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

// §I.3: the scalar type is uint8_t, shared by svBit and svLogic, and the
// canonical representation's chunk types are the listing's -- svBitVecVal a
// uint32_t and svLogicVecVal the s_vpi_vecval of two uint32_t, guarded by
// VPI_VECVAL with its pointer typedef beside it.
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

// §I.3: the time value is the s_vpi_time of an int32_t type, uint32_t high
// and low and a double real, guarded by VPI_TIME with its pointer typedef,
// and the three VPI time-type codes the listing defines beside it are the
// ones the sv_ names stand for.
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

// §I.3: the scope and open array handles are void pointers, and the version
// routine returns the implementation's string.
TEST(SvdpiSourceCode, TheHandlesAndTheVersionRoutineAreTheListings) {
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  EXPECT_TRUE((std::is_same<decltype(svDpiVersion()), const char*>::value));
  EXPECT_STREQ(svDpiVersion(), "1800-2005");
}

}  // namespace
