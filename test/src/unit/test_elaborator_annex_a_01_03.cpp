#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

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

TEST(ModuleParametersAndPorts, AnIndexedPortPartSelectByAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m3(c[k+:2]);\n"
      "  input [3:0] c;\n"
      "  int k;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a port expression selects with an expression "
                            "that is not constant",
                            1, "A.1.3"));
}

TEST(ModuleParametersAndPorts, AnIndexedPortPartSelectIsAsWideAsItsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m5(c[1+:3], d[3-:2]);\n"
      "  input [7:0] c;\n"
      "  input [7:0] d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].width, 3u);
  EXPECT_EQ(ports[1].width, 2u);
}

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

TEST(ModuleParametersAndPorts,
     ANetOrInterfacePortOfANonFixedDimensionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus; endinterface\n"
      "module m (bus c [], input wire a [], inout wire b [$]);\n"
      "endmodule\n",
      f);
  const std::string kRule =
      " takes fixed-size unpacked dimensions alone; a dynamic, associative or "
      "queue dimension belongs to a variable port";
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "net port 'a'" + kRule, 2, "A.1.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "net port 'b'" + kRule, 2, "A.1.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "interface port 'c'" + kRule,
                            2, "A.1.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "unpacked dimension of port 'b' is not a "
                             "constant expression",
                             2, "7.4.2"));
}

TEST(ModuleParametersAndPorts, ANetPortOfFixedSizeDimensionsIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m (input wire a [2], input wire b [0:3]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ModuleParametersAndPorts, AVariablePortTakesEveryVariableDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m (output int q [$], input var int a [string],\n"
      "          input var int w [*], input var int v []);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ModuleParametersAndPorts, AVariablePortsUnfoldableDimensionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m (input int a [W]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked dimension of port 'a' is not a constant "
                            "expression",
                            1, "7.4.2"));
}

}  // namespace
