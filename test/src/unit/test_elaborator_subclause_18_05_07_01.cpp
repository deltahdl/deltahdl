#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ForeachConstraintDimensions, LoopVarsWithinDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ForeachConstraintDimensions, ExceedsSingleDimensionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  constraint c { foreach (A[i, j]) A[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 2 loop variable(s) but array 'A' has only 1 dimension(s)", 3,
      "18.5.7.1"));
}

TEST(ForeachConstraintDimensions, ExceedsMultiDimensionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[i, j, k]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 3 loop variable(s) but array 'A' has only 2 dimension(s)", 3,
      "18.5.7.1"));
}

TEST(ForeachConstraintDimensions, InheritedArrayChecked) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  rand int arr[];\n"
             "endclass\n"
             "class D extends B;\n"
             "  constraint c { foreach (arr[i, j]) arr[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 2 loop variable(s) but array 'arr' has only 1 dimension(s)", 5,
      "18.5.7.1"));
}

TEST(ForeachConstraintDimensions, TrailingCommaNotCountedAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int A[];\n"
             "  constraint c { foreach (A[i,]) A[i] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ForeachConstraintDimensions, InteriorEmptySlotsCountedRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int A[2][3];\n"
             "  constraint c { foreach (A[,,k]) A[k] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 3 loop variable(s) but array 'A' has only 2 dimension(s)", 3,
      "18.5.7.1"));
}

TEST(ForeachConstraintDimensions, PackedDimensionCountsTowardLimit) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [3:0] A [2];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ForeachConstraintDimensions, MixedPackedUnpackedExampleWithinLimit) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [3:0][2:1] B [5:1][4];\n"
             "  constraint c { foreach (B[q, r, , s]) B[q][r] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ForeachConstraintDimensions, MixedPackedUnpackedExceededRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [3:0][2:1] B [5:1][4];\n"
             "  constraint c { foreach (B[a, b, c, d, e]) B[a][b] > 0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 5 loop variable(s) but array 'B' has only 4 dimension(s)", 3,
      "18.5.7.1"));
}

TEST(ForeachConstraintDimensions, RealArrayWithinDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real A[2][3];\n"
             "  constraint c { foreach (A[i, j]) A[i][j] > 0.0; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ForeachConstraintDimensions, RealArrayExceedsDimensionsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand real A[2][3];\n"
             "  constraint c { foreach (A[i, j, k]) A[i][j] > 0.0; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "lists 3 loop variable(s) but array 'A' has only 2 dimension(s)", 3,
      "18.5.7.1"));
}

}  // namespace
