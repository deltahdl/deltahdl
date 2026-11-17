#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesSimulation, InputPortPropagatesSourceValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  logic [7:0] result;\n"
      "  initial src = 8'hA5;\n"
      "  child u(.a(src), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(PortConnectionRulesSimulation,
     InoutPortConductsValueToParentUndiminished) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] pad);\n"
      "  assign pad = 8'h3C;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.pad(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

TEST(PortConnectionRulesSimulation, ExpressionSourceOnInputPortDrivesSink) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [7:0] p;\n"
                "  logic [7:0] q;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(p | q), .b(result));\n"
                "  initial begin p = 8'hF0; q = 8'h0F; end\n"
                "endmodule\n",
                "result"),
      0xFFu);
}

TEST(PortConnectionRulesSimulation,
     AssignmentCompatibleWidthConversionPropagates) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [3:0] narrow;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(narrow), .b(result));\n"
                "  initial narrow = 4'hA;\n"
                "endmodule\n",
                "result"),
      0x0Au);
}

TEST(PortConnectionRulesSimulation, OutputPortConnectionDrivesParentSink) {
  EXPECT_EQ(RunAndGet("module child(output logic [7:0] y);\n"
                      "  assign y = 8'h5A;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  logic [7:0] result;\n"
                      "  child u(.y(result));\n"
                      "endmodule\n",
                      "result"),
            0x5Au);
}

TEST(PortConnectionRulesSimulation,
     ContinuousAssignSourceFlowsThroughInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  logic [7:0] base;\n"
                "  logic [7:0] feed;\n"
                "  logic [7:0] result;\n"
                "  assign feed = base ^ 8'hFF;\n"
                "  child u(.a(feed), .b(result));\n"
                "  initial base = 8'h0F;\n"
                "endmodule\n",
                "result"),
      0xF0u);
}

TEST(PortConnectionRulesSimulation, TwoStateSourcePropagatesThroughInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  bit [7:0] two_state;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(two_state), .b(result));\n"
                "  initial two_state = 8'hC3;\n"
                "endmodule\n",
                "result"),
      0xC3u);
}

TEST(PortConnectionRulesSimulation, ParameterValueSourceDrivesInputPort) {
  EXPECT_EQ(
      RunAndGet("module child(input logic [7:0] a, output logic [7:0] b);\n"
                "  assign b = a;\n"
                "endmodule\n"
                "module top;\n"
                "  parameter logic [7:0] P = 8'h77;\n"
                "  logic [7:0] result;\n"
                "  child u(.a(P), .b(result));\n"
                "endmodule\n",
                "result"),
      0x77u);
}

TEST(PortConnectionRulesSimulation,
     PortsConnectedToInterfaceMembersFollowThem) {
  SimFixture f;
  auto out = RunCapture(
      "module gen(input clk, output reg o);\n"
      "  initial o = 0;\n"
      "  always @(posedge clk) o <= 1;\n"
      "endmodule\n"
      "interface gi(output bit clk, input o);\n"
      "endinterface\n"
      "module t;\n"
      "  gi dif();\n"
      "  gen dut(.clk(dif.clk), .o(dif.o));\n"
      "  initial begin\n"
      "    dif.clk = 0;\n"
      "    #10 dif.clk = 1;\n"
      "    #10 $display(\"%b %b %b\", dut.clk, dut.o, dif.o);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(PortConnectionKindsRun, AnEventCrossesAnInputVarAndARefPort) {
  for (const char* port : {"input var event e", "ref event e"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string("module c(") + port +
                             ");\n"
                             "  initial begin @e; $display(\"got %0t\", "
                             "$time); end\n"
                             "endmodule\n"
                             "module t;\n  event e;\n  c u(e);\n"
                             "  initial #2 ->e;\nendmodule\n",
                         f),
              "got 2\n")
        << port;
  }
}

TEST(PortConnectionKindsRun, DISABLED_AWildcardImportedVariableConnectsByName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n  logic [3:0] wc = 4'd7;\nendpackage\n"
                       "module c(input [3:0] a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n  import p::*;\n  c u(.a(wc));\nendmodule\n",
                       f),
            "7\n");
}

TEST(PortConnectionKindsRun,
     DISABLED_AnExplicitlyImportedVariableConnectsByName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n  logic [3:0] wc = 4'd7;\nendpackage\n"
                 "module c(input [3:0] a);\n"
                 "  initial #1 $display(\"%0d\", a);\n"
                 "endmodule\n"
                 "module t;\n  import p::wc;\n  c u(.a(wc));\nendmodule\n",
                 f),
      "7\n");
}

TEST(InoutStrengthRun, AWeakDriverInsideReadsWeakOutside) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c(inout w);\n"
                       "  assign (weak0, weak1) w = 1'b1;\n"
                       "endmodule\n"
                       "module t;\n  wire w;\n  c u(w);\n"
                       "  initial #1 $display(\"%v\", w);\nendmodule\n",
                       f),
            "We1\n");
}

TEST(InoutStrengthRun, AStrongDriverOutsideBeatsAWeakDriverInside) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module c(inout w);\n"
                       "  assign (weak0, weak1) w = 1'b1;\n"
                       "endmodule\n"
                       "module t;\n  wire w;\n  c u(w);\n  assign w = 1'b0;\n"
                       "  initial #1 $display(\"%v %b\", w, w);\nendmodule\n",
                       f),
            "St0 0\n");
}

TEST(NettypePortRun, MatchingNettypesResolveDriversOnBothSidesTogether) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package q;\n"
                 "  function automatic logic [3:0] rsum(input logic "
                 "[3:0] d[]);\n"
                 "    rsum = 0;\n"
                 "    foreach (d[i]) rsum += d[i];\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "import q::*;\n"
                 "nettype logic [3:0] snet with rsum;\n"
                 "module c(inout snet p);\n  assign p = 4'd2;\nendmodule\n"
                 "module t;\n  snet w;\n  assign w = 4'd3;\n  c u(w);\n"
                 "  initial #1 $display(\"%0d\", w);\nendmodule\n",
                 f),
      "5\n");
}

TEST(PortConnectionKindsRun, AScopedPackageVariableConnectsByName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n  logic [3:0] wc = 4'd7;\nendpackage\n"
                       "module c(input [3:0] a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n  c u(.a(p::wc));\nendmodule\n",
                       f),
            "7\n");
}

TEST(PortConnectionKindsRun, DISABLED_AnImportedVariableConnectsByPosition) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n  logic [3:0] wc = 4'd7;\nendpackage\n"
                       "module c(input [3:0] a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n  import p::wc;\n  c u(wc);\nendmodule\n",
                       f),
            "7\n");
}

}  // namespace
