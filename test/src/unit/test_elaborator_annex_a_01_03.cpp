#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// A.1.3 writes a non-ANSI port's port_reference as a port identifier and a
// constant_select, so an index, a bound or a width its select writes that is
// no constant expression is reported. A bit-select's index was never looked
// at, and a part-select whose bounds did not fold was taken for the whole
// vector (#7551).
TEST(ModuleParametersAndPorts, APortSelectByAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m1(a[i]);\n"
      "  input [3:0] a;\n"
      "  int i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a port expression selects with an expression "
                            "that is not constant",
                            1, "A.1.3"));
}

TEST(ModuleParametersAndPorts, APortPartSelectByAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m2(b[j:0]);\n"
      "  input [3:0] b;\n"
      "  int j;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a port expression selects with an expression "
                            "that is not constant",
                            1, "A.1.3"));
}

// A.1.3: a parameter is a constant expression, so a port selecting by one is
// accepted, as is a concatenation of constant selects.
TEST(ModuleParametersAndPorts, APortSelectByAParameterIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m4 #(parameter int K = 1) (a[K], {b[K+1:0], b[3]});\n"
      "  input [3:0] a;\n"
      "  input [3:0] b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
