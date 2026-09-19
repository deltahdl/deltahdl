#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <type_traits>

#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// §H.10: the C layer of the DPI defines one include file, svdpi.h, which the
// simulator provides as src/simulator/svdpi.h -- the one file dpi_c_type.h
// reaches the layer's types through, whose guard INCLUDED_SVDPI is the
// standard's own.
TEST(DpiIncludeFiles, TheCLayerDefinesOneIncludeFileSvdpiH) {
  EXPECT_EQ(DpiCLayerIncludeFile(), "svdpi.h");
  EXPECT_EQ(DpiCLayerIncludeFileCount(), 1u);
#ifdef INCLUDED_SVDPI
  const bool kFileIsIncluded = true;
#else
  const bool kFileIsIncluded = false;
#endif
  EXPECT_TRUE(kFileIsIncluded);
}

// §H.10: the file is implementation independent, the same for every
// simulator, and the actual file is shown in Annex I.
TEST(DpiIncludeFiles, TheFileIsImplementationIndependentAndShownInAnnexI) {
  EXPECT_TRUE(DpiCLayerIncludeFileIsImplementationIndependent());
  EXPECT_EQ(DpiAnnexShowingIncludeFile(), "Annex I");
}

// §H.10: the file defines the canonical representation -- the 2-state chunk
// svBitVecVal of 32 bits and the 4-state chunk svLogicVecVal of an aval and a
// bval word, one chunk per 32 bits.
TEST(DpiIncludeFiles, TheFileDefinesTheCanonicalRepresentation) {
  EXPECT_TRUE(
      DpiIncludeFileDefines(DpiIncludeFileContent::kCanonicalRepresentation));
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
  svLogicVecVal chunk = {};
  chunk.aval = 1;
  chunk.bval = 0;
  EXPECT_EQ(chunk.aval + chunk.bval, 1u);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
}

// §H.10: the file defines all basic types -- the scalars svScalar, svBit and
// svLogic, the vector chunks, the time value and the two handles.
TEST(DpiIncludeFiles, TheFileDefinesAllBasicTypes) {
  EXPECT_TRUE(DpiIncludeFileDefines(DpiIncludeFileContent::kBasicTypes));
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  EXPECT_GT(sizeof(svTimeVal), 0u);
}

// §H.10: the file defines all interface functions -- one of each family the
// annex specifies, referenced so that its declaration must be in the file.
TEST(DpiIncludeFiles, TheFileDefinesAllInterfaceFunctions) {
  EXPECT_TRUE(
      DpiIncludeFileDefines(DpiIncludeFileContent::kInterfaceFunctions));
  EXPECT_GT(sizeof(&svDpiVersion), 0u);
  EXPECT_GT(sizeof(&svGetBitselLogic), 0u);
  EXPECT_GT(sizeof(&svLow), 0u);
  EXPECT_GT(sizeof(&svGetArrayPtr), 0u);
  EXPECT_GT(sizeof(&svSetScope), 0u);
  EXPECT_GT(sizeof(&svPutUserData), 0u);
  EXPECT_GT(sizeof(&svGetTimeUnit), 0u);
  EXPECT_GT(sizeof(&svAckDisabledState), 0u);
}

}  // namespace
