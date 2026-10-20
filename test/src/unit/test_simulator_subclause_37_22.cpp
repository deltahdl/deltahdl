#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sim_context_types.h"
#include "simulator/vpi_dynamic_ranges.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.22 Object range: a range object carries the bounds of one array
// dimension. These tests observe the production helpers in vpi.cpp that apply
// the two numbered "Details" of the clause - what an empty range stands for
// (detail 1) and what vpiSize/vpiLeftRange/vpiRightRange report for it (detail
// 2). §37.17's range relations are woven onto the same helpers; that weaving is
// exercised in test_simulator_subclause_37_17.cpp.

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

// A design run with a PLI application registered, its ranges read back once
// the run is over.
class RangesOfARun : public VpiDesignRun {
 protected:
  // The integer value of a range's bound, -1 where it has none.
  static int BoundOf(vpiHandle bound) {
    if (bound == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(bound, &value);
    return value.value.integer;
  }

  // The size of the first range `obj` reaches and its bounds,
  // "size:left:right".
  static std::string FirstRangeOf(vpiHandle obj) {
    const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, obj);
    if (kRanges.empty()) return "(none)";
    vpiHandle range = kRanges.front();
    return std::to_string(vpi_get(vpiSize, range)) + ":" +
           std::to_string(BoundOf(vpi_handle(vpiLeftRange, range))) + ":" +
           std::to_string(BoundOf(vpi_handle(vpiRightRange, range)));
  }
};

// D1 and D2: the range of a dynamic array or a queue is empty while the array
// holds no element, and once it holds some is [0:n-1] over its current
// elements, a range the variable's own vpiLeftRange and vpiRightRange read as
// well (#7025).
TEST_F(RangesOfARun, ADynamicArraysRangeFollowsItsCurrentSize) {
  Run("module top;\n"
      "  int arr1 []; int empty1 []; int q [$];\n"
      "  initial begin arr1 = new[2]; q = {5, 6, 7}; end\n"
      "endmodule\n");
  EXPECT_EQ(FirstRangeOf(By("top.arr1")), "2:0:1");
  EXPECT_EQ(FirstRangeOf(By("top.q")), "3:0:2");
  EXPECT_EQ(FirstRangeOf(By("top.empty1")), "0:-1:-1");
  EXPECT_EQ(BoundOf(vpi_handle(vpiRightRange, By("top.arr1"))), 1);
}

// D1: a range that belongs to no array is a fixed one, and so is one of a
// dynamic array that was given no bounds to follow its elements with; a
// dynamic array holding no range has none whose bounds follow it.
TEST(ObjectRange, OnlyADynamicArraysFirstRangeFollowsIt) {
  VpiObject loose;
  loose.type = vpiRange;
  EXPECT_EQ(VpiDynamicRangeOf(&loose), nullptr);
  QueueObject store;
  VpiObject array;
  array.queue = &store;
  VpiObject fixed;
  fixed.type = vpiRange;
  fixed.parent = &array;
  array.children = {&fixed};
  EXPECT_EQ(VpiDynamicRangeOf(&array), nullptr);
  VpiObject bound;
  bound.type = vpiConstant;
  VpiObject bare;
  bare.queue = &store;
  bare.children = {&bound};
  EXPECT_EQ(VpiDynamicRangeOf(&bare), nullptr);
}

}  // namespace
}  // namespace delta
