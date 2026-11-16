#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_constraint_item_places.h"
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

void ExpectTooManyLoopVariables(ItemPlace place, const std::string& decl,
                                const std::string& item, const char* tail) {
  ElabFixture f;
  ElabOk(ItemIn(place, decl, item), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), tail, 5, "18.5.7.1"))
      << ItemPlaceName(place) << ": " << item;
}

void ExpectLoopVariablesAccepted(ItemPlace place, const std::string& decl,
                                 const std::string& item) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(ItemIn(place, decl, item), f))
      << ItemPlaceName(place) << ": " << item;
}

const char* const kTwoOverOne = "lists 2 loop variable(s) but array '";
const char* const kThreeOverTwo = "lists 3 loop variable(s) but array '";

TEST(ForeachConstraintDimensions, TwoOverAQueueOrAnAssociativeArrayRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kClassBlock, "int q[$], z;",
                             "foreach (q[i, j]) z != q[i];", kTwoOverOne);
  ExpectTooManyLoopVariables(ItemPlace::kClassBlock, "int a[int], z;",
                             "foreach (a[i, j]) z != a[i];", kTwoOverOne);
}

TEST(ForeachConstraintDimensions, ThreeOverAnArrayOfArraysRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kClassBlock, "int q[$][2], z;",
                             "foreach (q[i, j, k]) z != q[i][j];",
                             kThreeOverTwo);
  ExpectTooManyLoopVariables(ItemPlace::kClassBlock, "int d[][], z;",
                             "foreach (d[i, j, k]) z != d[i][j];",
                             kThreeOverTwo);
}

TEST(ForeachConstraintDimensions, TwoOverAnArrayOfArraysAccepted) {
  ExpectLoopVariablesAccepted(ItemPlace::kClassBlock, "int q[$][2], z;",
                              "foreach (q[i, j]) z != q[i][j];");
  ExpectLoopVariablesAccepted(ItemPlace::kClassBlock, "int d[][], z;",
                              "foreach (d[i, j]) z != d[i][j];");
}

TEST(ForeachConstraintDimensions, DISABLED_TwoOverAStringRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kClassBlock, "string s; int z;",
                             "foreach (s[i, j]) z != s[i];", kTwoOverOne);
}

TEST(ForeachConstraintDimensions, OneOverAStringAccepted) {
  ExpectLoopVariablesAccepted(ItemPlace::kClassBlock, "string s; int z;",
                              "foreach (s[i]) z != s[i];");
}

TEST(ForeachConstraintDimensions, TwoOverOneOutOfBlockRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kOutOfBlock, "int A[4], z;",
                             "foreach (A[i, j]) z != A[i];", kTwoOverOne);
}

TEST(ForeachConstraintDimensions, DISABLED_TwoOverOneInAnInlineBlockRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kInline, "int A[4], z;",
                             "foreach (A[i, j]) z != A[i];", kTwoOverOne);
}

TEST(ForeachConstraintDimensions,
     DISABLED_TwoOverOneInAScopeRandomizeRejected) {
  ExpectTooManyLoopVariables(ItemPlace::kScope, "int A[4], z;",
                             "foreach (A[i, j]) z != A[i];", kTwoOverOne);
}

TEST(ForeachConstraintDimensions, OneOverOneBeyondTheClassAccepted) {
  for (ItemPlace place : kItemPlacesBeyondTheClass) {
    ExpectLoopVariablesAccepted(place, "int A[4], z;",
                                "foreach (A[i]) z != A[i];");
  }
}

void ExpectLoopVariableUndeclared(const std::string& item) {
  ElabFixture f;
  ElabOk(ItemIn(ItemPlace::kClassBlock, "rand bit [3:0] A[3];", item), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'i'",
                            5, "23.9"))
      << item;
}

TEST(ForeachLoopVariableScope,
     DISABLED_ALoopVariableNamedAfterItsForeachIsUndeclared) {
  ExpectLoopVariableUndeclared("foreach (A[i]) A[i] == 1; i == 0;");
}

TEST(ForeachLoopVariableScope,
     DISABLED_ALoopVariableNamedInAnotherConstraintIsUndeclared) {
  ExpectLoopVariableUndeclared(
      "foreach (A[i]) A[i] == 1; } constraint k2 { i == 0;");
}

TEST(ForeachLoopVariableScope, ALoopVariableNamedInsideItsForeachIsAccepted) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(ItemIn(ItemPlace::kClassBlock, "rand bit [3:0] A[3];",
                            "foreach (A[i]) A[i] == i;"),
                     f));
}

}  // namespace
