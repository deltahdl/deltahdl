#include <gtest/gtest.h>

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

}  // namespace
