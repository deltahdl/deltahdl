#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, SizeOfFixedFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfFixedInnerDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfQueueFirstDimensionIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $size(q, 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfQueueInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][$];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, SizeOfWildcardAssocInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][*];\n"
      "  int n;\n"
      "  initial n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, LeftOfDynamicInnerDimensionIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $left(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$left' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, InnerVariableDimInDeclInitializerIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            3, "20.7.1"));
}

TEST(ArrayQueryVariableDim, FixedDimInDeclInitializerIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n = $size(a, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, IndexedElementQueryIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a[2], 1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, ParameterDimensionIndexIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter int D = 2;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'a'",
                            5, "20.7.1"));
}

TEST(ArrayQueryVariableDim, LocalparamDimensionIndexAtFixedDimIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam int D = 3;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $size(a, D);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, DimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, UnpackedDimensionsIsUnaffected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int a[3][][5];\n"
      "  int n;\n"
      "  initial n = $unpacked_dimensions(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionNames20_7_1) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int a[3][][5];\n"
             "  int n;\n"
             "  initial n = $size(a, 2);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot query variable-sized dimension 2 of array "
                            "'a'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim, SizeOfDynamicInnerDimensionInAForStepIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int qa[3][][5];\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $size(qa, 2))\n"
      "      i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$size' cannot query "
                            "variable-sized dimension 2 of array 'qa'",
                            5, "20.7.1"));
}

TEST(ArrayQueryVariableDim,
     LowOfDynamicInnerDimensionInAnAssertionPassStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int pa[4][][2];\n"
      "  int n;\n"
      "  logic ready;\n"
      "  initial assert (ready) n = $low(pa, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$low' cannot query "
                            "variable-sized dimension 2 of array 'pa'",
                            5, "20.7.1"));
}

TEST(ArrayQueryVariableDim,
     HighOfQueueInnerDimensionInAnAssertionFailStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int qb[2][$];\n"
      "  int n;\n"
      "  logic go;\n"
      "  initial assert (go) else n = $high(qb, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$high' cannot query "
                            "variable-sized dimension 2 of array 'qb'",
                            5, "20.7.1"));
}

TEST(ArrayQueryVariableDim,
     IncrementOfWildcardAssocInnerDimensionInARandcaseItemIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int wa[2][*];\n"
      "  int n;\n"
      "  initial randcase 1: n = $increment(wa, 2); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$increment' cannot query "
                            "variable-sized dimension 2 of array 'wa'",
                            4, "20.7.1"));
}

TEST(ArrayQueryVariableDim,
     RightOfDynamicInnerDimensionInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int ra[3][][6];\n"
      "  int n;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { n = $right(ra, 2); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array query function '$right' cannot query "
                            "variable-sized dimension 2 of array 'ra'",
                            6, "20.7.1"));
}

}  // namespace
