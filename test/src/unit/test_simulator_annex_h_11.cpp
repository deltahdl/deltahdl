#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

// §H.11: normalized ranges are used for accessing SystemVerilog arrays,
// with the exception of formal arguments specified as open arrays, which
// keep the ranges of the actual.
TEST(DpiArrayAccess, SizedArraysAreAccessedByNormalizedRangesOpenArraysNot) {
  EXPECT_EQ(DpiRangesUsedForAccessing(false), DpiArrayRanges::kNormalized);
  EXPECT_EQ(DpiRangesUsedForAccessing(true), DpiArrayRanges::kOfTheActual);
}

// §H.11: a dimension declared [L:R] is normalized to [size-1:0] whichever
// way it runs, and one already so declared is its own normalization.
TEST(DpiArrayAccess, ANormalizedRangeRunsFromSizeMinusOneDownToZero) {
  EXPECT_EQ(DpiNormalizedRange({3, 1}).low, 2);
  EXPECT_EQ(DpiNormalizedRange({3, 1}).high, 0);
  EXPECT_EQ(DpiNormalizedRange({2, 5}).low, 3);
  EXPECT_EQ(DpiNormalizedRange({2, 5}).high, 0);
  EXPECT_EQ(DpiNormalizedRange({-1, -8}).low, 7);
  EXPECT_EQ(DpiNormalizedRange({7, 0}).low, 7);
  EXPECT_EQ(DpiNormalizedRange({7, 0}).high, 0);
}

// §H.11: the ranges a sized formal `int a [3:1][2:5]` is accessed by are
// [2:0] and [3:0], and the same declared ranges stay [3:1] and [2:5] for an
// open array formal.
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

// §H.11 with §H.11.4 and §H.11.5: under normalized ranges an element is
// reached by its index counted from the low bound -- a[3][2] of
// `int a [3:1][2:5]` is a[2][0] in C -- and a bit by its distance from the
// LSB -- a[4] of `bit [4:7] a` is bit 3.
TEST(DpiArrayAccess, NormalizedIndicesCountFromTheLowBoundAndTheLsb) {
  const std::vector<uint32_t> kIndices =
      DpiCIndicesOfUnpackedElement({{3, 1}, {2, 5}}, {3, 2});
  ASSERT_EQ(kIndices.size(), 2u);
  EXPECT_EQ(kIndices[0], 2u);
  EXPECT_EQ(kIndices[1], 0u);
  EXPECT_EQ(DpiNormalizedBitIndex({4, 7}, 4), 3);
  EXPECT_EQ(DpiNormalizedBitIndex({4, 7}, 7), 0);
}

// §H.11 with §H.12.2: an open array formal is the exception, its handle
// reporting the actual's own bounds -- [3:1] and [2:5] as declared, left
// and right as written rather than normalized.
TEST(DpiArrayAccess, AnOpenArrayKeepsTheActualsOwnRanges) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {3, 1}, {2, 5}};
  SvOpenArrayDesc desc;
  desc.data = nullptr;
  desc.n_dims = 3;
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
