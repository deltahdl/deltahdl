#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

namespace {

// §H.12.1: the programmer always has the choice between a sized formal and
// an open one; a sized formal is passed by reference with no overhead and
// is directly accessible as a normalized array, an open one by handle with
// some overhead and mostly indirectly accessible.
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

// The clause's two actuals, both 64 by 8 elements of 16 packed bits:
// logic [15:0] a_64x8 [63:0][7:0] and logic [31:16] b_64x8 [64:1][-1:-8].
std::vector<SvActualDimension> PackedOfA() { return {{15, 0}}; }
std::vector<SvActualDimension> UnpackedOfA() { return {{63, 0}, {7, 0}}; }
std::vector<SvActualDimension> PackedOfB() { return {{31, 16}}; }
std::vector<SvActualDimension> UnpackedOfB() { return {{64, 1}, {-1, -8}}; }

// The clause's f1, `input logic [] i [][]`: every dimension unsized.
DpiFormalDimension Unsized() { return DpiFormalDimension{false, {0, 0}}; }

// The clause's f2, `input logic [31:16] i [64:1][-1:-8]`: every dimension
// sized as b_64x8 is declared.
DpiFormalDimension Sized(SvActualDimension range) {
  return DpiFormalDimension{true, range};
}

void ExpectRange(const SvActualDimension& range, int32_t left, int32_t right) {
  EXPECT_EQ(range.low, left);
  EXPECT_EQ(range.high, right);
}

// §H.12.1: f1(b_64x8) lets C code use the normalized packed range and the
// actual's original unpacked ranges, [15:0][64:1][-1:-8].
TEST(DpiActualRanges, AnOpenFormalKeepsTheActualsUnpackedRanges) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 64, 1);
  ExpectRange(kRanges[2], -1, -8);
}

// §H.12.1: f1(a_64x8) is the same C code over a_64x8's own ranges,
// [15:0][63:0][7:0], the open formal's ranges being the actual's per call.
TEST(DpiActualRanges, AnOpenFormalsRangesAreTheActualsPerCall) {
  const std::vector<SvActualDimension> kRanges = DpiCRangesAtCall(
      Unsized(), {Unsized(), Unsized()}, PackedOfA(), UnpackedOfA());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 63, 0);
  ExpectRange(kRanges[2], 7, 0);
}

// §H.12.1: f2(b_64x8) has C code use normalized ranges throughout,
// [15:0][0:63][0:7], every index of a sized dimension normalized to 0 and
// up.
TEST(DpiActualRanges, ASizedFormalIsNormalizedThroughout) {
  const std::vector<SvActualDimension> kRanges =
      DpiCRangesAtCall(Sized({31, 16}), {Sized({64, 1}), Sized({-1, -8})},
                       PackedOfB(), UnpackedOfB());
  ASSERT_EQ(kRanges.size(), 3u);
  ExpectRange(kRanges[0], 15, 0);
  ExpectRange(kRanges[1], 0, 63);
  ExpectRange(kRanges[2], 0, 7);
}

// §H.12.1 with §H.7.6: under a sized formal the programmer maps the actual's
// ranges onto C-style ones, an index counting from the low bound of its
// dimension -- b_64x8[64][-1] is element [63][7] of f2's normalized array
// and b_64x8[1][-8] its element [0][0] -- where a [n:0]name[0:k] style
// declaration, the clause's tip, needs no mapping.
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
