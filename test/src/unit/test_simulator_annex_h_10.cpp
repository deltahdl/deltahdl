#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <type_traits>

#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

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

TEST(DpiIncludeFiles, TheFileIsImplementationIndependentAndShownInAnnexI) {
  EXPECT_TRUE(DpiCLayerIncludeFileIsImplementationIndependent());
  EXPECT_EQ(DpiAnnexShowingIncludeFile(), "Annex I");
}

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

TEST(DpiIncludeFiles, TheFileDefinesAllBasicTypes) {
  EXPECT_TRUE(DpiIncludeFileDefines(DpiIncludeFileContent::kBasicTypes));
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBitVecVal, uint32_t>::value));
  EXPECT_TRUE((std::is_same<svScope, void*>::value));
  EXPECT_TRUE((std::is_same<svOpenArrayHandle, void*>::value));
  EXPECT_GT(sizeof(svTimeVal), 0u);
}

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
