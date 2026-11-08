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

TEST(ObjectRange, EmptyRangeStandsForDynamicQueueAndAssociativeDimensions) {
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kAssoc));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kDynamic));
  EXPECT_TRUE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kQueue));
}

TEST(ObjectRange, FixedDimensionsAreNotEmptyRanges) {
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kPacked));
  EXPECT_FALSE(VpiDimensionRangeIsEmpty(VpiDimensionKind::kFixedUnpacked));
}

TEST(ObjectRange, EmptyRangeHasZeroSizeAndNullBounds) {
  VpiObject left;
  VpiObject right;
  VpiRangeDesc range;
  range.empty = true;
  range.left_expr = &left;
  range.right_expr = &right;
  range.size = 7;

  EXPECT_EQ(VpiRangeSize(range), 0);
  EXPECT_EQ(VpiRangeLeftRange(range), nullptr);
  EXPECT_EQ(VpiRangeRightRange(range), nullptr);
}

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

class RangesOfARun : public VpiDesignRun {
 protected:
  static int BoundOf(vpiHandle bound) {
    if (bound == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(bound, &value);
    return value.value.integer;
  }

  static std::string FirstRangeOf(vpiHandle obj) {
    const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, obj);
    if (kRanges.empty()) return "(none)";
    vpiHandle range = kRanges.front();
    return std::to_string(vpi_get(vpiSize, range)) + ":" +
           std::to_string(BoundOf(vpi_handle(vpiLeftRange, range))) + ":" +
           std::to_string(BoundOf(vpi_handle(vpiRightRange, range)));
  }
};

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
