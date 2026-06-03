#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.7.1: in a foreach iterative constraint the number of loop variables shall
// not exceed the number of dimensions of the array. A two-dimensional array
// iterated with two loop variables is within that limit and elaborates.
TEST(ForeachConstraintDimensions, LoopVarsWithinDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: a one-dimensional (dynamic) array iterated with two loop variables
// names more dimensions than the array has, which is an error.
TEST(ForeachConstraintDimensions, ExceedsSingleDimensionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  constraint c { foreach (A[i, j]) A[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: three loop variables exceed the two dimensions of the array.
TEST(ForeachConstraintDimensions, ExceedsMultiDimensionRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[i, j, k]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: the iterated array may be an inherited property; its dimensionality
// is resolved through the base class, so an over-long loop-variable list on an
// inherited one-dimensional array is still an error.
TEST(ForeachConstraintDimensions, InheritedArrayChecked) {
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  rand int arr[];\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { foreach (arr[i, j]) arr[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: a trailing run of commas may be omitted, so a trailing empty slot
// does not count as a loop variable. 'A[i,]' names one loop variable over a
// one-dimensional array and is within the limit.
TEST(ForeachConstraintDimensions, TrailingCommaNotCountedAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  constraint c { foreach (A[i,]) A[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: an empty interior loop-variable slot still corresponds to a
// dimension, so it counts toward the limit. 'A[,,k]' names a third dimension on
// a two-dimensional array, which is an error.
TEST(ForeachConstraintDimensions, InteriorEmptySlotsCountedRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[,,k]) A[k] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
