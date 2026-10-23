#include <gtest/gtest.h>

#include <string>

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

// A.1.3: an indexed part-select of a port is as wide as the width it writes,
// neither one bit nor the whole vector it selects from (#7552).
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

// A.1.3's ansi_port_declaration gives a port declared with a net_port_header
// or an interface_port_header unpacked_dimensions alone, each a constant range
// or size (A.2.5), so a dynamic dimension on an interface port, a dynamic
// dimension on a net port and a queue dimension on an inout net are each
// reported. The dynamic ones were taken with no report, and the queue was
// reported as a dimension that is not a constant expression (§7.4.2).
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

// A net port's constant range and constant size are the unpacked_dimensions
// A.1.3 gives it, and draw no report.
TEST(ModuleParametersAndPorts, ANetPortOfFixedSizeDimensionsIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m (input wire a [2], input wire b [0:3]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A.1.3 gives a port declared with a variable_port_header variable_dimensions,
// which A.2.5 makes a dynamic, an associative or a queue dimension as well as
// a fixed one, so none of these four variable ports is reported. The queue and
// the two associative ones were reported as unpacked dimensions that are not
// constant expressions (§7.4.2).
TEST(ModuleParametersAndPorts, AVariablePortTakesEveryVariableDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m (output int q [$], input int a [string], input int w [*],\n"
      "          input var int v []);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A variable port's fixed dimension is still folded, and one whose size names
// nothing the module declares is still reported.
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
