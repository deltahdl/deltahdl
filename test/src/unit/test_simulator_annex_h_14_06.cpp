#include <gtest/gtest.h>

#include <cstdlib>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

void MyFunc(svLogicPackedArrRef r) {
  const svLogicVec32 kValue = {0xC0FFEE42u, 0x0000000Fu};
  svPutLogicVec32(r, &kValue, 32);
}

TEST(DpiBinaryCompatibleExportCall, DynamicAllocationNeedsNoSvdpiSrc) {
  EXPECT_FALSE(DpiSvdpiSrcIsNeededForExportCall(true));
  EXPECT_TRUE(DpiSvdpiSrcIsNeededForExportCall(false));
  EXPECT_EQ(DpiCompatibilityOfApplication(false),
            DpiApplicationCompatibility::kBinary);
}

TEST(DpiBinaryCompatibleExportCall, TheExportWritesTheAllocatedRepresentation) {
  svLogicVec32 my_r[SV_CANONICAL_SIZE(32)] = {};

  auto r = static_cast<svLogicPackedArrRef>(
      malloc(static_cast<size_t>(svSizeOfLogicPackedArr(32))));
  ASSERT_NE(r, nullptr);
  MyFunc(r);
  svGetLogicVec32(my_r, r, 32);
  free(r);

  EXPECT_EQ(SV_CANONICAL_SIZE(32), 1);
  EXPECT_EQ(my_r[0].c, 0xC0FFEE42u);
  EXPECT_EQ(my_r[0].d, 0x0000000Fu);
}

}  // namespace
