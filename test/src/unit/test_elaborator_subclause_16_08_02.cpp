#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.8.2: the actual of an inout or output local variable formal argument is,
// in its entirety, a reference to a local variable in scope at the instance:
// v + 1 is an expression and g a module variable, while top3's v is a local.
TEST(LocalFormalElaboration, AnOutwardActualIsALocalVariable) {
  const char* const kReport =
      "the actual of the inout or output local variable formal 'lv' of 'sub' "
      "shall be a reference to a local variable in scope";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int g;\n"
      "  sequence sub(local inout int lv);\n"
      "    (a, lv += 1);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v;\n"
      "    (1, v = 0) ##1 sub(v + 1);\n"
      "  endsequence\n"
      "  sequence top2;\n"
      "    sub(g);\n"
      "  endsequence\n"
      "  sequence top3;\n"
      "    int v;\n"
      "    (1, v = 0) ##1 sub(v);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.8.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 12, "16.8.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 16, "16.8.2"));
}

// §16.8.2: one local variable is not the actual of two inout or output local
// variable formal arguments of an instance.
TEST(LocalFormalElaboration, OneLocalBoundToTwoOutwardFormalsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence sub(local inout int x, local output int y);\n"
      "    (a, x += 1, y = 2);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v, w;\n"
      "    (1, v = 0, w = 0) ##1 sub(v, v) ##1 sub(v, w);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the local variable 'v' is the actual of two "
                            "inout or output local variable formals of 'sub'",
                            8, "16.8.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the local variable 'w'", 8,
                             "16.8.2"));
}

// §16.8.2: no match of a sequence leaves an output local variable formal
// argument unassigned at its completion: the b alternative of sub assigns no
// o, while every match of sub2 assigns it.
TEST(LocalFormalElaboration, AnOutputUnassignedByAMatchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence sub(local output int o);\n"
      "    (a, o = 1) or b;\n"
      "  endsequence\n"
      "  sequence sub2(local output int o);\n"
      "    (a, o = 1) or (b, o = 2);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output local variable formal argument 'o' of "
                            "'sub' is unassigned at the completion of a match",
                            3, "16.8.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "of 'sub2' is unassigned", 6,
                             "16.8.2"));
}

// §16.8.2: an instance of a sequence with an inout or output local variable
// formal argument admits no empty match: sub's body, repeated from zero, does.
TEST(LocalFormalElaboration, AnOutwardInstanceAdmittingAnEmptyMatchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence sub(local inout int o);\n"
      "    (a, o += 1)[*0:1];\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v;\n"
      "    (1, v = 0) ##1 sub(v) ##1 (v == 1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'sub', which has an inout or output local "
                            "variable formal argument, admits an empty match",
                            8, "16.8.2"));
}

// §16.8.2: triggered and matched apply to no instance of a sequence with an
// input or inout local variable formal argument.
TEST(LocalFormalElaboration, TriggeredOfAnInstanceWithAnInputLocalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence sub(local input int x);\n"
      "    @(posedge clk) a ##1 (x == 1);\n"
      "  endsequence\n"
      "  initial wait (sub(1).triggered);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "triggered may not be applied to an instance of "
                            "'sub', which has an input or inout local variable "
                            "formal argument",
                            6, "16.8.2"));
}

// §16.8.2: the actual of an input local variable formal argument references
// no local variable unassigned where the instance stands, as v is.
TEST(LocalFormalElaboration, AnUnassignedLocalAsAnInputActualIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence sub(local input int x);\n"
      "    a ##1 (x == 1);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v;\n"
      "    sub(v) ##1 a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the local variable 'v' is referenced at a point "
                            "where it is unassigned",
                            8, "16.8.2"));
}

}  // namespace
