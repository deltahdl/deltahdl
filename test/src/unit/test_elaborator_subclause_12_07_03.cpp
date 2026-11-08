#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, ForeachLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachMultiDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) matrix[i][j] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachTooManyLoopVarsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i] = j;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarCountAtDimLimitOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i][j] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarAssignIsNotAnUndeclaredName) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin i = 0; arr[i] = 1; end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'i'",
                             4, "23.9"));
}

TEST(LoopStatementElaboration, ForeachLoopVarIncrementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachAssignArrayElementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarNonblockingAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i <= 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarMemberWriteThroughHandleOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class node;\n"
      "  int count;\n"
      "endclass\n"
      "module m;\n"
      "  bit preds [node];\n"
      "  initial begin\n"
      "    foreach (preds[p]) p.count = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration,
     ForeachLoopVarMemberElementWriteThroughHandleOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class node;\n"
      "  bit succ [node];\n"
      "endclass\n"
      "module m;\n"
      "  bit preds [node];\n"
      "  node q;\n"
      "  initial begin\n"
      "    foreach (preds[p]) p.succ[q] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarRedeclaredByInnerForLoopOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) for (int i = 0; i < 2; i++) arr[i] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarRedeclaredInInnerBlockOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      int i;\n"
      "      i = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarAssignedByInnerForInitIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) for (i = 0; i < 2; i++) arr[i] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarAssignedAfterInnerForLoopIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      for (int i = 0; i < 2; i++) arr[i] = 0;\n"
      "      i = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            6, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarBitSelectAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i[0] = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (arr[arr]) x = arr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'arr' may not have the same "
                            "name as the array it iterates over",
                            5, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLaterLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (matrix[i, matrix]) x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'matrix' may not have the "
                            "same name as the array it iterates over",
                            5, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial foreach (arr[i]) assert (ok) i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial foreach (arr[i]) assert (ok) else i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            4, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarAssignedInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial foreach (arr[i]) randcase 1: i = 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            3, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial foreach (arr[i]) begin\n"
      "    randsequence(main)\n"
      "      main : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            5, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachLoopVarAssignedInARandsequenceWeightCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int j;\n"
      "  initial foreach (arr[i]) begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { i = 1; };\n"
      "      a : { j = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach loop variable 'i' is read-only and cannot "
                            "be assigned",
                            6, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInAnAssertionPassStatementIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial assert (ok) foreach (arr[i, j]) arr[i] = j;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInAnAssertionFailStatementIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  logic ok;\n"
      "  initial assert (ok) else foreach (arr[i, j]) arr[i] = j;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      4, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInARandcaseItemIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial randcase 1: foreach (arr[i, j]) arr[i] = j; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      3, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInARandsequenceCodeBlockIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { foreach (arr[i, j]) arr[i] = j; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      5, "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachInARandsequenceWeightCodeBlockIsHeldToTheArrayDimensionCount) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int k;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 1 { foreach (arr[i, j]) arr[i] = j; };\n"
      "      a : { k = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'arr' has only 1 dimension(s)",
      6, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverBlockLocalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int a [4];\n"
      "    foreach (a[i, j, k]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 3 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachOverFunctionLocalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    int a [4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverFormalArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f(int a [4]);\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverClassPropertyCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    int a [4];\n"
      "    function void f();\n"
      "      foreach (a[i, j]) begin end\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 5,
      "12.7.3"));
}

TEST(LoopStatementElaboration,
     ForeachOverAUnitClassPropertyCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int a [4];\n"
      "  function void f();\n"
      "    foreach (a[i, j]) begin end\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachCountsTheArrayItsBlockDeclares) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4][4];\n"
      "  initial begin\n"
      "    int a [4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'a' has only 1 dimension(s)", 5,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverBlockArrayHidingAModuleArrayOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  initial begin\n"
      "    int a [4][4];\n"
      "    foreach (a[i, j]) begin end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachOverRealArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r [4];\n"
      "  initial foreach (r[i, j]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'r' has only 1 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverStringArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string s [2][3];\n"
      "  initial foreach (s[i, j, k, l]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 4 loop variables but array 's' has only 3 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverStringArrayWalksItsCharacters) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string s [2][3];\n"
      "  initial foreach (s[i, j, k]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachOverAStringWalksItsCharacters) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  int c;\n"
      "  function automatic int f(string t);\n"
      "    int n = 0;\n"
      "    foreach (t[i]) n++;\n"
      "    return n;\n"
      "  endfunction\n"
      "  initial foreach (s[i]) c++;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachOverAStringWithTwoLoopVariablesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial foreach (s[i, j]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 's' has only 1 dimension(s)", 3,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachOverClassHandleArrayCountsItsDimensions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C; endclass\n"
      "  C h [4];\n"
      "  initial foreach (h[i, j]) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach lists 2 loop variables but array 'h' has only 1 dimension(s)", 4,
      "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarWrittenInsideAnExpressionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4]; int x;\n"
      "  initial foreach (a[i]) begin\n"
      "    x = i++;\n"
      "    x = (i += 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* msg =
      "foreach loop variable 'i' is read-only and cannot be assigned";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 4, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 5, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarIncrementStatementReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  initial foreach (a[i]) i++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "foreach loop variable 'i' is read-only and cannot be assigned", 3,
      "12.7.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LoopStatementElaboration, ForeachLoopVarPassedToAWritingFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  task automatic t_out(output int v); v = 0; endtask\n"
      "  task automatic t_io(inout int v); v = 0; endtask\n"
      "  task automatic t_ref(ref int v); v = 0; endtask\n"
      "  initial foreach (a[i]) begin\n"
      "    t_out(i);\n"
      "    t_io(.v(i));\n"
      "    t_ref(i);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* msg =
      "foreach loop variable 'i' is read-only and cannot be assigned";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 7, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 8, "12.7.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 9, "12.7.3"));
}

TEST(LoopStatementElaboration, ForeachLoopVarPassedToAReadingFormalOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  task automatic t_in(input int v); endtask\n"
      "  task automatic t_cref(const ref int v); endtask\n"
      "  int n;\n"
      "  initial foreach (a[i]) begin\n"
      "    t_in(i);\n"
      "    t_cref(i);\n"
      "    n = a.sum();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
