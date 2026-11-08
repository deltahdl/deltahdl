#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

TEST(DpiArrayAccess, SizedArraysAreAccessedByNormalizedRangesOpenArraysNot) {
  EXPECT_EQ(DpiRangesUsedForAccessing(false), DpiArrayRanges::kNormalized);
  EXPECT_EQ(DpiRangesUsedForAccessing(true), DpiArrayRanges::kOfTheActual);
}

TEST(DpiArrayAccess, ANormalizedRangeRunsFromSizeMinusOneDownToZero) {
  EXPECT_EQ(DpiNormalizedRange({3, 1}).low, 2);
  EXPECT_EQ(DpiNormalizedRange({3, 1}).high, 0);
  EXPECT_EQ(DpiNormalizedRange({2, 5}).low, 3);
  EXPECT_EQ(DpiNormalizedRange({2, 5}).high, 0);
  EXPECT_EQ(DpiNormalizedRange({-1, -8}).low, 7);
  EXPECT_EQ(DpiNormalizedRange({7, 0}).low, 7);
  EXPECT_EQ(DpiNormalizedRange({7, 0}).high, 0);
}

TEST(DpiArrayAccess, ASizedFormalsRangesAreNormalizedAndAnOpenArraysKept) {
  const std::vector<SvActualDimension> kDeclared = {{3, 1}, {2, 5}};
  const std::vector<SvActualDimension> kSized =
      DpiRangesForAccessing(kDeclared, false);
  ASSERT_EQ(kSized.size(), 2u);
  EXPECT_EQ(kSized[0].low, 2);
  EXPECT_EQ(kSized[0].high, 0);
  EXPECT_EQ(kSized[1].low, 3);
  EXPECT_EQ(kSized[1].high, 0);
  const std::vector<SvActualDimension> kOpen =
      DpiRangesForAccessing(kDeclared, true);
  ASSERT_EQ(kOpen.size(), 2u);
  EXPECT_EQ(kOpen[0].low, 3);
  EXPECT_EQ(kOpen[0].high, 1);
  EXPECT_EQ(kOpen[1].low, 2);
  EXPECT_EQ(kOpen[1].high, 5);
}

TEST(DpiArrayAccess, NormalizedIndicesCountFromTheLowBoundAndTheLsb) {
  const std::vector<uint32_t> kIndices =
      DpiCIndicesOfUnpackedElement({{3, 1}, {2, 5}}, {3, 2});
  ASSERT_EQ(kIndices.size(), 2u);
  EXPECT_EQ(kIndices[0], 2u);
  EXPECT_EQ(kIndices[1], 0u);
  EXPECT_EQ(DpiNormalizedBitIndex({4, 7}, 4), 3);
  EXPECT_EQ(DpiNormalizedBitIndex({4, 7}, 7), 0);
}

TEST(DpiArrayAccess, AnOpenArrayKeepsTheActualsOwnRanges) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {3, 1}, {2, 5}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 3;
  desc.has_packed_part = 1;
  desc.ranges = kRanges;
  desc.elem_size = 0;
  svOpenArrayHandle h = &desc;
  EXPECT_EQ(svLeft(h, 1), 3);
  EXPECT_EQ(svRight(h, 1), 1);
  EXPECT_EQ(svLow(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1), 3);
  EXPECT_EQ(svLeft(h, 2), 2);
  EXPECT_EQ(svRight(h, 2), 5);
  EXPECT_EQ(svLow(h, 2), 2);
  EXPECT_EQ(svHigh(h, 2), 5);
}

}  // namespace
