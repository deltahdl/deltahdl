#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.22 Object range: a range object carries the bounds of one array
// dimension. These tests observe the production helpers in vpi.cpp that apply
// the two numbered "Details" of the clause - what an empty range stands for
// (detail 1) and what vpiSize/vpiLeftRange/vpiRightRange report for it (detail
// 2). §37.17's range relations are woven onto the same helpers; that weaving is
// exercised in test_simulator_clause_37_17.cpp.

// D1: an empty range represents an associative-array dimension, an empty
// dynamic array or queue, and a range from a typespec for any of those. Each
// such dimension kind classifies as empty.
TEST(ObjectRange, EmptyRangeStandsForDynamicQueueAndAssociativeDimensions) {
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kAssoc));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kDynamic));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kQueue));
}

// D1: a fixed packed or unpacked dimension has real bounds, so it is not an
// empty range.
TEST(ObjectRange, FixedDimensionsAreNotEmptyRanges) {
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kPacked));
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kFixedUnpacked));
}

// D2: for an empty range vpiSize returns 0, and vpiLeftRange and vpiRightRange
// each return NULL.
TEST(ObjectRange, EmptyRangeHasZeroSizeAndNullBounds) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = true;
  range.left_expr = &left;  // present but suppressed because the range is empty
  range.right_expr = &right;
  range.size = 7;

  EXPECT_EQ(VpiRangeSize(range), 0);
  EXPECT_EQ(VpiRangeLeftRange(range), nullptr);
  EXPECT_EQ(VpiRangeRightRange(range), nullptr);
}

// D2: a non-empty range reports its element count and both bound expressions.
TEST(ObjectRange, NonEmptyRangeReportsSizeAndBoundExpressions) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = false;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 10;

  EXPECT_EQ(VpiRangeSize(range), 10);
  EXPECT_EQ(VpiRangeLeftRange(range), &left);
  EXPECT_EQ(VpiRangeRightRange(range), &right);
}

// D2 edge: a non-empty range may have a zero element count without becoming an
// empty range; its bounds are still reported.
TEST(ObjectRange, NonEmptyRangeWithZeroCountStillReportsBounds) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = false;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 0;

  EXPECT_EQ(VpiRangeSize(range), 0);
  EXPECT_EQ(VpiRangeLeftRange(range), &left);
  EXPECT_EQ(VpiRangeRightRange(range), &right);
}

}  // namespace
}  // namespace delta
