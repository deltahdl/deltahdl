#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArraySubroutineArgValidation, ActualWithFewerUnpackedDimsIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  task automatic fun(int a[3:1][3:1]); endtask\n"
      "  int b[3:1];\n"
      "  initial fun(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array argument 'b' has 1 unpacked dimension(s) "
                            "but formal 'a' has 2",
                            4, "7.7"));
}

TEST(ArraySubroutineArgValidation, ActualWithDifferentFasterDimSizeIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  task automatic fun(int a[3:1][3:1]); endtask\n"
      "  int b[3:1][4:1];\n"
      "  initial fun(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension 2 of array argument 'b' has "
                            "size 4 but formal 'a' has size 3",
                            4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     ActualWithDifferentSlowestDimSizeIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  function automatic int g(int a[3][2]); return 0; endfunction\n"
      "  int b[4][2];\n"
      "  int r;\n"
      "  initial r = g(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension 1 of array argument 'b' has "
                            "size 4 but formal 'a' has size 3",
                            5, "7.7"));
}

TEST(ArraySubroutineArgValidation, ActualWithSameSizesInOtherRangesElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic fun(int a[3:1][3:1]); endtask\n"
             "  int b[1:3][0:2];\n"
             "  initial fun(b);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation,
     DynamicOuterActualWithMatchingDimElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic fun(int a[3:1][3:1]); endtask\n"
             "  int b[][3];\n"
             "  initial fun(b);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, DynamicOuterActualWithOtherDimIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  task automatic fun(int a[3:1][3:1]); endtask\n"
      "  int b[][4];\n"
      "  initial fun(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension 2 of array argument 'b' has "
                            "size 4 but formal 'a' has size 3",
                            4, "7.7"));
}

TEST(ArraySubroutineArgValidation, QueueActualForTwoDimFormalIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  task automatic fun(int a[3:1][3:1]); endtask\n"
      "  int q[$];\n"
      "  initial fun(.a(q));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array argument 'q' has 1 unpacked dimension(s) "
                            "but formal 'a' has 2",
                            4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     ActualOfLogicElementsForIntFormalIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  task automatic fun(int a[3:1][3:1]); endtask\n"
      "  logic b[3:1][3:1];\n"
      "  initial fun(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "element type of array argument 'b' is not "
                            "equivalent to that of formal 'a'",
                            4, "7.7"));
}

TEST(ArraySubroutineArgValidation,
     ActualOfEventElementsForIntFormalIsRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  function automatic int g(int a[3]); return 0; endfunction\n"
      "  event b[3];\n"
      "  int r;\n"
      "  initial r = g(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "element type of array argument 'b' is not "
                            "equivalent to that of formal 'a'",
                            5, "7.7"));
}

TEST(ArraySubroutineArgValidation, ActualOfEquivalentElementsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int word_t;\n"
             "  task automatic fun(word_t a[3:1][3:1]); endtask\n"
             "  bit signed [31:0] b[3:1][3:1];\n"
             "  int c[1:3][2:0];\n"
             "  initial begin\n"
             "    fun(b);\n"
             "    fun(c);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, ActualOfArrayTypedefElementsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int row_t[3];\n"
             "  task automatic fun(int a[3][3]); endtask\n"
             "  row_t b[3];\n"
             "  initial fun(b);\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation,
     DpiOpenArrayOutputJudgedWhicheverWayItIsBound) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  import \"DPI-C\" function void f(output int o[]);\n"
      "  import \"DPI-C\" function void g(input int a, output int o[]);\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    f(q);\n"
      "    f(.o(q));\n"
      "    g(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kReport =
      "a dynamic array or queue cannot be passed to the open-array output "
      "argument of DPI import 'f'";
  EXPECT_TRUE(ReportedError(diags, kReport, 6, "7.7"));
  EXPECT_TRUE(ReportedError(diags, kReport, 7, "7.7"));
}

TEST(ArraySubroutineArgValidation, EnumElementTypesComparedByIdentity) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {A, B} e1_t;\n"
      "  typedef enum {C, D} e2_t;\n"
      "  typedef e1_t e3_t;\n"
      "  e2_t y[2];\n"
      "  e3_t z[2];\n"
      "  function void f(e1_t a[2]); endfunction\n"
      "  initial begin\n"
      "    f(y);\n"
      "    f(z);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "element type of array argument 'y' is not "
                            "equivalent to that of formal 'a'",
                            9, "7.7"));
  for (const auto& d : diags) EXPECT_NE(d.loc.line, 10u) << d.message;
}

}  // namespace
