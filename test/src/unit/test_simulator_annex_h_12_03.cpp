#include <gtest/gtest.h>

#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

TEST(DpiAccessFunctions, TwoFamiliesCopyThroughABufferOrYieldAnAddress) {
  EXPECT_EQ(DpiSideProvidingCanonicalBuffer(), DpiMemorySide::kC);
  EXPECT_TRUE(DpiAccessCopiesThroughCanonicalBuffer(
      DpiOpenArrayAccess::kCopyElementToCanonicalBuffer));
  EXPECT_TRUE(DpiAccessCopiesThroughCanonicalBuffer(
      DpiOpenArrayAccess::kCopyElementFromCanonicalBuffer));
  EXPECT_FALSE(DpiAccessCopiesThroughCanonicalBuffer(
      DpiOpenArrayAccess::kAddressOfArray));
  EXPECT_FALSE(DpiAccessCopiesThroughCanonicalBuffer(
      DpiOpenArrayAccess::kAddressOfElement));
}

TEST(DpiAccessFunctions, EachAccessHasItsLibraryFunction) {
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kCopyElementToCanonicalBuffer,
                              false),
            "svGetBitArrElemVecVal");
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kCopyElementToCanonicalBuffer,
                              true),
            "svGetLogicArrElemVecVal");
  EXPECT_EQ(DpiAccessFunction(
                DpiOpenArrayAccess::kCopyElementFromCanonicalBuffer, false),
            "svPutBitArrElemVecVal");
  EXPECT_EQ(DpiAccessFunction(
                DpiOpenArrayAccess::kCopyElementFromCanonicalBuffer, true),
            "svPutLogicArrElemVecVal");
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kAddressOfArray, false),
            "svGetArrayPtr");
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kAddressOfArray, true),
            "svGetArrayPtr");
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kAddressOfElement, false),
            "svGetArrElemPtr");
  EXPECT_EQ(DpiAccessFunction(DpiOpenArrayAccess::kAddressOfElement, true),
            "svGetArrElemPtr");
}

TEST(DpiAccessFunctions, TheCopyAndTheAddressReachTheSameElement) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  desc.data = data;
  desc.n_dims = 2;
  desc.has_packed_part = 1;
  desc.ranges = kRanges;
  desc.elem_size = sizeof(svBitVecVal);
  svOpenArrayHandle h = &desc;

  svBitVecVal buffer = 0x5Au;
  svPutBitArrElem1VecVal(h, &buffer, 2);
  auto* element = static_cast<svBitVecVal*>(svGetArrElemPtr1(h, 2));
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(*element, 0x5Au);

  *element = 0xC3u;
  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 2);
  EXPECT_EQ(out, 0xC3u);
}

}  // namespace
