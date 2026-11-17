#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(NonAnsiPortExpressionSimulation, SplitPortsFillHalvesOfTheVector) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module split_ports(a[7:4], a[3:0]);\n"
                       "  input [7:0] a;\n"
                       "  initial #1 $display(\"hi %0d lo %0d a %0d\", a[7:4], "
                       "a[3:0], a);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  split_ports s(4'd10, 4'd5);\n"
                       "endmodule\n",
                       f),
            "hi 10 lo 5 a 165\n");
}

TEST(NonAnsiPortExpressionSimulation, SplitOutputPortsCarryHalvesOut) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sp(y[7:4], y[3:0]);\n"
                       "  output [7:0] y;\n"
                       "  assign y = 8'hC3;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] h, l;\n"
                       "  sp s(h, l);\n"
                       "  initial #1 $display(\"h %h l %h y %h\", h, l, s.y);\n"
                       "endmodule\n",
                       f),
            "h c l 3 y c3\n");
}

TEST(NonAnsiPortExpressionSimulation, ExplicitPortsReachConcatAndBitSelect) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module renamed_concat(.a({b, c}), f, .g(h[1]));\n"
                       "  input b, c;\n"
                       "  output [3:0] f;\n"
                       "  output [1:0] h;\n"
                       "  assign f = 4'd9;\n"
                       "  assign h = 2'b11;\n"
                       "  initial #1 $display(\"a %0d f %0d g %0d\", {b, c} + "
                       "3'd2, f, top.pg + 2'd2);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] pf;\n"
                       "  wire pg;\n"
                       "  renamed_concat r(.a(2'b11), .f(pf), .g(pg));\n"
                       "endmodule\n",
                       f),
            "a 5 f 9 g 3\n");
}

TEST(NonAnsiPortExpressionSimulation, ConcatPortAndTwoPortsOnOneInout) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module complex_ports({c, d}, .e(f));\n"
                       "  input c, d;\n"
                       "  output [3:0] f;\n"
                       "  assign f = {2'b10, c, d};\n"
                       "endmodule\n"
                       "module same_port(.a(i), .b(i));\n"
                       "  inout wire [3:0] i;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] pe, w1, w2;\n"
                       "  assign w1 = 4'h6;\n"
                       "  complex_ports cp(2'b01, pe);\n"
                       "  same_port sp(w1, w2);\n"
                       "  initial #1 $display(\"pe %b w2 %h\", pe, w2);\n"
                       "endmodule\n",
                       f),
            "pe 1001 w2 6\n");
}

TEST(NonAnsiPortExpressionSimulation,
     ASignedVariableDeclarationMakesThePortSigned) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(f);\n"
                       "  output [7:0] f;\n"
                       "  logic signed [7:0] f;\n"
                       "  assign f = -8'sd3;\n"
                       "  initial #1 $display(\"%0d %0d\", f, f < 0);\n"
                       "endmodule\n"
                       "module t;\n  wire [7:0] w;\n  m u(w);\nendmodule\n",
                       f),
            "-3 1\n");
}

TEST(NonAnsiPortExpressionSimulation, ANamedConnectionReachesAnEscapedPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(\\a+b );\n"
                       "  input \\a+b ;\n"
                       "  initial #1 $display(\"%b\", \\a+b );\n"
                       "endmodule\n"
                       "module t;\n  wire w = 1'b1;\n"
                       "  child c(.\\a+b (w));\nendmodule\n",
                       f),
            "1\n");
}

TEST(NonAnsiPortExpressionSimulation,
     DISABLED_AConcatenatedPortCarriesValuesBothWays) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(.p({a, e}));\n"
                       "  input a;\n"
                       "  output e;\n"
                       "  assign e = ~a;\n"
                       "endmodule\n"
                       "module t;\n  wire [1:0] w;\n"
                       "  assign w[1] = 1'b1;\n  m u(w);\n"
                       "  initial #1 $display(\"%b %b\", u.a, w[0]);\n"
                       "endmodule\n",
                       f),
            "1 0\n");
}

std::string BodyPortWidth(const std::string& direction,
                          const std::string& override_by,
                          const std::string& after, SimFixture& f) {
  return RunCapture(
      "module m(a);\n"
      "  parameter W = 4;\n"
      "  localparam L = W + 1;\n"
      "  " +
          direction +
          " a;\n"
          "  initial $display(\"%0d\", $bits(a));\n"
          "endmodule\n"
          "module t;\n  wire [9:0] w;\n  m " +
          override_by + " u(w);\n" + after + "endmodule\n",
      f);
}

TEST(NonAnsiPortRangeOverride, DISABLED_AnInputRangeTakesTheOverride) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("input [W-1:0]", "#(7)", "", f), "7\n");
}

TEST(NonAnsiPortRangeOverride, DISABLED_AnOutputRangeTakesTheOverride) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("output [W-1:0]", "#(7)", "", f), "7\n");
}

TEST(NonAnsiPortRangeOverride, DISABLED_AnInoutRangeTakesTheOverride) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("inout [W-1:0]", "#(7)", "", f), "7\n");
}

TEST(NonAnsiPortRangeOverride, DISABLED_ALocalparamRangeTakesTheOverride) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("input [L-1:0]", "#(7)", "", f), "8\n");
}

TEST(NonAnsiPortRangeOverride, DISABLED_AnOverrideByNameReachesTheRange) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("input [W-1:0]", "#(.W(7))", "", f), "7\n");
}

TEST(NonAnsiPortRangeOverride, DISABLED_ADefparamReachesTheRange) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("input [W-1:0]", "", "  defparam u.W = 7;\n", f),
            "7\n");
}

TEST(NonAnsiPortRangeOverride, WithoutAnOverrideTheDefaultWidthHolds) {
  SimFixture f;
  EXPECT_EQ(BodyPortWidth("input [W-1:0]", "", "", f), "4\n");
}

TEST(NonAnsiPortRangeOverride, AnAnsiPortRangeTakesTheOverride) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m #(parameter W = 4)(input [W-1:0] a);\n"
                 "  initial $display(\"%0d\", $bits(a));\n"
                 "endmodule\n"
                 "module t;\n  wire [6:0] w;\n  m #(7) u(w);\nendmodule\n",
                 f),
      "7\n");
}

TEST(NonAnsiPortRangeOverride, AHeaderParameterReachesABodyPortRange) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m #(parameter W = 4)(a);\n"
                 "  input [W-1:0] a;\n"
                 "  initial $display(\"%0d\", $bits(a));\n"
                 "endmodule\n"
                 "module t;\n  wire [6:0] w;\n  m #(7) u(w);\nendmodule\n",
                 f),
      "7\n");
}

std::string BodyInterfacePortDesign(const std::string& keyword,
                                    const std::string& name,
                                    const std::string& type,
                                    const std::string& connection) {
  return keyword + " " + name + "(a);\n  " + type +
         " a;\n  initial #1 a.gnt = a.req;\n  initial #3;\nend" + keyword +
         "\n" +
         "module t;\n  simple_bus sb_intf();\n  initial sb_intf.req = 1;\n  " +
         name + " u(" + connection +
         ");\n  initial #2 $display(\"%b\", sb_intf.gnt);\nendmodule\n";
}

std::string RunInterfacePortDesign(const std::string& design, SimFixture& f) {
  return RunCapture(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "  modport target(input req, output gnt);\n"
      "endinterface\n" +
          design,
      f);
}

TEST(NonAnsiInterfacePorts,
     DISABLED_ABodyInterfacePortDenotesThePositionalActual) {
  SimFixture f;
  EXPECT_EQ(
      RunInterfacePortDesign(
          BodyInterfacePortDesign("module", "memMod", "simple_bus", "sb_intf"),
          f),
      "1\n");
}

TEST(NonAnsiInterfacePorts, DISABLED_ABodyInterfacePortDenotesTheNamedActual) {
  SimFixture f;
  EXPECT_EQ(RunInterfacePortDesign(
                BodyInterfacePortDesign("module", "memMod", "simple_bus",
                                        ".a(sb_intf)"),
                f),
            "1\n");
}

TEST(NonAnsiInterfacePorts, DISABLED_ABodyInterfacePortThroughAModport) {
  SimFixture f;
  EXPECT_EQ(RunInterfacePortDesign(
                BodyInterfacePortDesign("module", "memMod", "simple_bus.target",
                                        "sb_intf"),
                f),
            "1\n");
}

TEST(NonAnsiInterfacePorts,
     DISABLED_OneDeclarationBindsEachPortToItsOwnActual) {
  SimFixture f;
  EXPECT_EQ(RunInterfacePortDesign(
                "module memMod(a, b);\n"
                "  simple_bus a, b;\n"
                "  initial #1 begin a.gnt = 1; b.gnt = 0; end\n"
                "endmodule\n"
                "module t;\n  simple_bus x(), y();\n  memMod mem(y, x);\n"
                "  initial #2 $display(\"%b %b\", x.gnt, y.gnt);\nendmodule\n",
                f),
            "0 1\n");
}

TEST(NonAnsiInterfacePorts, DISABLED_AnInterfaceBodyDeclaresAnInterfacePort) {
  for (const char* type : {"simple_bus", "simple_bus.target"}) {
    SimFixture f;
    EXPECT_EQ(
        RunInterfacePortDesign(
            BodyInterfacePortDesign("interface", "outer", type, "sb_intf"), f),
        "1\n")
        << type;
  }
}

TEST(NonAnsiInterfacePorts, DISABLED_AProgramBodyDeclaresAnInterfacePort) {
  for (const char* type : {"simple_bus", "simple_bus.target"}) {
    SimFixture f;
    EXPECT_EQ(
        RunInterfacePortDesign(
            BodyInterfacePortDesign("program", "prog", type, "sb_intf"), f),
        "1\n")
        << type;
  }
}

TEST(NonAnsiInterfacePorts, AnAnsiInterfacePortDenotesItsActual) {
  SimFixture f;
  EXPECT_EQ(RunInterfacePortDesign(
                "module memMod(simple_bus a);\n"
                "  initial #1 a.gnt = a.req;\n"
                "endmodule\n"
                "module t;\n  simple_bus sb_intf();\n"
                "  initial sb_intf.req = 1;\n  memMod mem(sb_intf);\n"
                "  initial #2 $display(\"%b\", sb_intf.gnt);\nendmodule\n",
                f),
            "1\n");
}

}  // namespace
