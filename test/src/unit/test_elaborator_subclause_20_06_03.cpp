#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IsunboundedElab, AnArgumentThatNamesNoParameterIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v = 5;\n"
      "  initial begin\n"
      "    if ($isunbounded(v)) $display(\"x\");\n"
      "    $display(\"%0d\", $isunbounded(v + 1));\n"
      "  end\n"
      "  function int g();\n"
      "    return $isunbounded(3);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  const char* message =
      "'$isunbounded' asks about a parameter, so its argument must name one";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 4, "20.6.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 5, "20.6.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 8, "20.6.3"));
}

TEST(IsunboundedElab, AParameterNameIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  parameter int Q = 2;\n"
      "endpackage\n"
      "module t #(parameter int A = $);\n"
      "  parameter int B = 1;\n"
      "  localparam int C = 4;\n"
      "  initial $display(\"%0d %0d %0d %0d\", $isunbounded(A), "
      "$isunbounded(B), $isunbounded(C), $isunbounded(p::Q));\n"
      "endmodule\n",
      f, "t");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IsunboundedElab, AHierarchicalParameterNameIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub #(parameter int P = $); endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  sub a[2]();\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    r1 = $isunbounded(s.P);\n"
      "    r2 = $isunbounded(t.s.P);\n"
      "    r3 = $isunbounded(a[0].P);\n"
      "  end\n"
      "endmodule\n",
      f, "t");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IsunboundedElab, AHierarchicalNameOfAVariableIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; int v; endmodule\n"
      "module t;\n"
      "  sub s();\n"
      "  int result;\n"
      "  initial result = $isunbounded(s.v);\n"
      "endmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$isunbounded' asks about a parameter, so its argument must name one", 5,
      "20.6.3"));
}

}  // namespace
