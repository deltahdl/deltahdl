#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.6.3: the argument of $isunbounded shall be the name of a parameter, so a
// variable, an expression or a literal is an error wherever the call stands.
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
  const char* kMessage =
      "the argument of '$isunbounded' shall be the name of a parameter";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "20.6.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "20.6.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 8, "20.6.3"));
}

// §20.6.3: a parameter of the port list or of the body, a localparam and a
// package-qualified parameter are each a parameter's name.
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

}  // namespace
