#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.7's `fun` example: an actual with fewer unpacked dimensions than the
// formal cannot be associated with it.
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

// The same example's size error: the faster-varying dimension of the actual
// has 4 elements where the formal's has 3.
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

// The sizes are compared in the slowest-varying dimension too, and a formal
// written with sizes rather than ranges is compared the same way.
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

// §7.7 accepts `int b[1:3][0:2]` for `fun`: the ranges differ but the number
// of dimensions and the size of each are the same.
TEST(ArraySubroutineArgValidation, ActualWithSameSizesInOtherRangesElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task automatic fun(int a[3:1][3:1]); endtask\n"
             "  int b[1:3][0:2];\n"
             "  initial fun(b);\n"
             "endmodule\n"));
}

// A dynamic slowest dimension has no size until run time, so only the fixed
// dimension behind it is compared; a matching one elaborates.
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

// A queue actual still has to bring as many unpacked dimensions as the formal
// has, whatever its size turns out to be.
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

// §7.7's `logic b[3:1][3:1]` for `fun`: logic is 4-state where int is 2-state,
// so the element types are not equivalent.
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

// §7.7's `event b[3:1][3:1]` for `fun`: an event is no integral type at all.
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

// §6.22.2 makes `bit signed [31:0]` equivalent to int, and a typedef name
// equivalent to the type it names, so both actuals are associated with the
// int formal.
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

// An element type that is itself an unpacked array by typedef brings its own
// dimensions behind the declaration's, so `row_t b[3]` has the two dimensions
// of the formal.
TEST(ArraySubroutineArgValidation, ActualOfArrayTypedefElementsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int row_t[3];\n"
             "  task automatic fun(int a[3][3]); endtask\n"
             "  row_t b[3];\n"
             "  initial fun(b);\n"
             "endmodule\n"));
}

// §7.7: a dynamic array or queue may not be the actual of a DPI import's
// open-array output formal, whichever way the call binds it, by position or
// by name. A call that binds no actual to that formal has nothing to judge.
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

// §7.7 with §6.22.2: an actual whose elements are a different enumeration from
// the formal's is not equivalent to it, however wide the two are; one whose
// elements are a typedef renaming the formal's enumeration is.
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
