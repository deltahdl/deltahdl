#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

TEST(DpiActualRanges, SizedAndOpenFormalsTradePerformanceForConvenience) {
  EXPECT_TRUE(DpiProgrammerChoosesFormalSizing());
  EXPECT_EQ(DpiPassingModeOfSizing(DpiFormalArraySizing::kSized),
            DpiPassingMode::kByReference);
  EXPECT_EQ(DpiPassingModeOfSizing(DpiFormalArraySizing::kOpen),
            DpiPassingMode::kByHandle);
  EXPECT_FALSE(DpiSizingHasOverhead(DpiFormalArraySizing::kSized));
  EXPECT_TRUE(DpiSizingHasOverhead(DpiFormalArraySizing::kOpen));
  EXPECT_EQ(DpiAccessibilityOfSizing(DpiFormalArraySizing::kSized),
            DpiArrayAccessibility::kDirectlyAsNormalizedArray);
  EXPECT_EQ(DpiAccessibilityOfSizing(DpiFormalArraySizing::kOpen),
            DpiArrayAccessibility::kMostlyIndirectlyThroughTheHandle);
}

std::vector<SvActualDimension> PackedOfA() { return {{15, 0}}; }
std::vector<SvActualDimension> UnpackedOfA() { return {{63, 0}, {7, 0}}; }
std::vector<SvActualDimension> PackedOfB() { return {{31, 16}}; }
std::vector<SvActualDimension> UnpackedOfB() { return {{64, 1}, {-1, -8}}; }

DpiFormalDimension Unsized() { return DpiFormalDimension{false, {0, 0}}; }

DpiFormalDimension Sized(SvActualDimension range) {
  return DpiFormalDimension{true, range};
}

void ExpectRange(const SvActualDimension& range, int32_t left, int32_t right) {
  EXPECT_EQ(range.low, left);
  EXPECT_EQ(range.high, right);
}

TEST(DpiActualRanges, AnOpenFormalKeepsTheActualsUnpackedRanges) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 64, 1);
  ExpectRange(kRanges[2], -1, -8);
}

TEST(DpiActualRanges, AnOpenFormalsRangesAreTheActualsPerCall) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfA(), UnpackedOfA());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 63, 0);
  ExpectRange(kRanges[2], 7, 0);
}

TEST(DpiActualRanges, ASizedFormalIsNormalizedThroughout) {
  const std::vector<SvActualDimension> kRanges =
      DpiCRangesAtCall(Sized({31, 16}), {Sized({64, 1}), Sized({-1, -8})},
                       PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 0, 63);
  ExpectRange(kRanges[2], 0, 7);
}

TEST(DpiActualRanges, TheActualsIndicesMapOntoTheNormalizedOnes) {
  std::vector<uint32_t> first =
      DpiCIndicesOfUnpackedElement(UnpackedOfB(), {64, -1});
  ASSERT_EQ(first.size(), 2u);
  EXPECT_EQ(first[0], 63u);
  EXPECT_EQ(first[1], 7u);
  std::vector<uint32_t> last =
      DpiCIndicesOfUnpackedElement(UnpackedOfB(), {1, -8});
  EXPECT_EQ(last[0], 0u);
  EXPECT_EQ(last[1], 0u);
  std::vector<uint32_t> tip =
      DpiCIndicesOfUnpackedElement({{0, 63}, {0, 7}}, {5, 3});
  EXPECT_EQ(tip[0], 5u);
  EXPECT_EQ(tip[1], 3u);
}

}  // namespace
