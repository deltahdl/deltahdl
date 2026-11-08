#include <gtest/gtest.h>

#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDpiOpenArrayReport =
    "a dynamic array or queue cannot be passed to the open-array output "
    "argument of DPI import 'f'";

TEST(ArraySubroutineArgValidation, TaskWithMultipleArrayArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task copy(input int src[4], output int dst[4]);\n"
             "    dst = src;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, ArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DynamicArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DynamicActualToFixedFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, FixedActualToDynamicFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsDynamicArray) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation, DpiOpenArrayInoutRejectsDynamicArray) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(inout int a[]);\n"
      "  int dyn[];\n"
      "  initial f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsQueue) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int q[$];\n"
      "  initial f(q);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation, DpiOpenArrayInputAcceptsDynamicArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(input int a[]);\n"
             "  int dyn[];\n"
             "  initial f(dyn);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputAcceptsFixedArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(output int a[]);\n"
             "  int fixed[4];\n"
             "  initial f(fixed);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForkBranch) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial fork\n"
      "    f(dyn);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForInitialization) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial for (int i = f(dyn); i < 1; i = i + 1) r = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForStep) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; f(dyn)) i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionPassStatement) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (1) f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionFailStatement) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (1) else f(dyn);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandcaseItem) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial randcase\n"
      "    1 : f(dyn);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCodeBlock) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { f(dyn); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function void f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { f(dyn); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 7, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssignmentLvalueSelect) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int arr[4];\n"
      "  initial arr[f(dyn)] = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInDelayControl) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial #(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInCycleDelay) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial ##(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInForCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int i;\n"
      "  initial for (i = 0; f(dyn) < 1; i = i + 1) i = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInAssertionExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial assert (f(dyn) == 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRepeatEventCount) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  logic clk;\n"
      "  initial r = repeat (f(dyn)) @(posedge clk) 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInBlockVariableInitializer) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    static int r = f(dyn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInEventExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial @(f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInEventIffCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  logic clk;\n"
      "  initial @(posedge clk iff f(dyn)) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandcaseWeight) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial randcase\n"
      "    f(dyn) : r = 1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInCaseItemExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  int r;\n"
      "  initial case (r)\n"
      "    f(dyn) : r = 1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInUnpackedDimension) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    int a[f(dyn)];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 5, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceWeightExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : one := (f(dyn));\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRandJoinExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join (f(dyn)) one two;\n"
      "      one : { ; };\n"
      "      two : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRandJoinItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : rand join one(f(dyn)) two;\n"
      "      void one(int x) : { ; };\n"
      "      two : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceIfCondition) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (f(dyn)) one;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceIfBranchArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceElseBranchArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) one(0) else one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRepeatCount) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat (f(dyn)) one;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceRepeatItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : repeat (1) one(f(dyn));\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (f(dyn)) 0 : one; endcase;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseItemExpression) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0) f(dyn) : one; endcase;\n"
      "      one : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputRejectsDynamicArrayInRandsequenceCaseItemArgument) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  import \"DPI-C\" function int f(output int a[]);\n"
      "  int dyn[];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0) 0 : one(f(dyn)); endcase;\n"
      "      void one(int x) : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kDpiOpenArrayReport, 6, "7.7"));
}

}  // namespace
