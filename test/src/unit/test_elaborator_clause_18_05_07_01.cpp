#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.5.7.1: in a foreach iterative constraint the number of loop variables
// shall not exceed the number of dimensions of the array. A two-dimensional
// array iterated with two loop variables is within that limit and elaborates.
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

// 18.5.7.1: the "dimensions of the array" a foreach may iterate include a
// variable's packed dimensions, not just its unpacked ones. A 'bit [3:0] A [2]'
// has one packed and one unpacked dimension, so two loop variables are within
// the limit. This isolates packed-dimension counting: were only the unpacked
// dimension counted, this two-variable list would exceed the single dimension
// and be rejected. That it is accepted shows the packed dimension counts.
TEST(ForeachConstraintDimensions, PackedDimensionCountsTowardLimit) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [3:0] A [2];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: a variable with two packed and two unpacked dimensions (the shape
// of the clause's own worked example, 'bit [3:0][2:1] B [5:1][4]') has four
// dimensions in all. Four loop-variable slots — here one left empty in the
// middle — are exactly at the limit and elaborate, exercising the counting of
// multiple packed dimensions alongside the unpacked ones.
TEST(ForeachConstraintDimensions, MixedPackedUnpackedExampleWithinLimit) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [3:0][2:1] B [5:1][4];\n"
             "  constraint c { foreach (B[q, r, , s]) B[q][r] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: the same four-dimensional packed/unpacked variable is exceeded by a
// fifth loop variable, confirming the shall-not-exceed limit is computed over
// the combined packed-plus-unpacked dimension total, not the unpacked count
// alone.
TEST(ForeachConstraintDimensions, MixedPackedUnpackedExceededRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [3:0][2:1] B [5:1][4];\n"
             "  constraint c { foreach (B[a, b, c, d, e]) B[a][b] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: the array a foreach iterates may be of any packed or unpacked
// array type, which includes an unpacked array of a real element type (rand
// real variables are legal). A real array has no packed dimensions, so its
// dimension count is just its unpacked dimensions; a two-dimensional real array
// iterated with two loop variables is within the limit and elaborates.
TEST(ForeachConstraintDimensions, RealArrayWithinDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real A[2][3];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0.0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.7.1: the loop-variable-count limit is enforced for a real array just as
// for an integral one — three loop variables exceed the two dimensions of a
// real array and are rejected.
TEST(ForeachConstraintDimensions, RealArrayExceedsDimensionsRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real A[2][3];\n"
             "  constraint c { foreach (A[i, j, k]) A[i][j] > 0.0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
