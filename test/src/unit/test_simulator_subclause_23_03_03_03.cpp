#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortReceivesValueFromParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h42;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForNetsSimulation,
     UnconnectedInputNetPortProducesHighZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToExpressionReceivesComputedValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h40;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv + 8'd2), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForNetsSimulation, OutputNetPortDrivesParentVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForNetsSimulation, OutputNetPortDrivesParentNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire [7:0] y);\n"
      "  assign y = 8'hBE;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.y(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToParameterReceivesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter logic [7:0] P = 8'h6D;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(P), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6Du);
}

TEST(PortConnectionRulesForNetsSimulation,
     InputNetPortConnectedToLocalparamReceivesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wire [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  localparam logic [7:0] L = 8'h2E;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(L), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x2Eu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InoutNetPortPropagatesValueToParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(PortConnectionRulesForNetsSimulation,
     InoutNetPortDriverResolvesWithParentDriver) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'b1111_zzzz;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  assign bus = 8'bzzzz_0000;\n"
      "  child u(.data(bus));\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(PortConnectionRulesForNetsSimulation, NetDrivenToTheZItHoldsDoesNotWake) {
  const char* const kDrivers[] = {
      "program p(inout wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endprogram\n",
      "module p(inout wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n",
      "module p(output wire [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n",
      "module p(output [7:0] data);\n"
      "  logic [7:0] drv = 8'bz;\n"
      "  assign data = drv;\n"
      "  initial begin #2 drv = 8'hAA; #1; end\n"
      "endmodule\n"};
  for (const char* driver : kDrivers) {
    SimFixture f;
    EXPECT_EQ(RunCapture(std::string(driver) +
                             "module top;\n"
                             "  wire [7:0] data;\n"
                             "  p pi(data);\n"
                             "  always @(data) $display(\"data=%0d at %0t\", "
                             "data, $time);\n"
                             "endmodule\n",
                         f),
              "data=170 at 2\n")
        << driver;
  }
  SimFixture g;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  wire [7:0] data;\n"
                       "  wire b;\n"
                       "  logic [7:0] d = 8'bz;\n"
                       "  assign data = d;\n"
                       "  assign b = 1'bz;\n"
                       "  always @(data) $display(\"data=%0d at %0t\", data, "
                       "$time);\n"
                       "  always @(b) $display(\"b at %0t\", $time);\n"
                       "  initial #2 d = 8'hAA;\n"
                       "endmodule\n",
                       g),
            "data=170 at 2\n");
}

TEST(PortConnectionRulesForNetsSimulation, NetPortsStartAtHighZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub(input wire [3:0] i, input var logic [3:0] "
                       "vi,\n"
                       "           input [3:0] ii, output wire [3:0] ow);\n"
                       "  initial $display(\"i=%b vi=%b ii=%b ow=%b\", i, vi, "
                       "ii, ow);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] o;\n"
                       "  sub s(.i(), .vi(), .ii(), .ow(o));\n"
                       "  initial #1 $display(\"o=%b\", o);\n"
                       "endmodule\n",
                       f),
            "i=zzzz vi=xxxx ii=zzzz ow=zzzz\no=zzzz\n");
}

TEST(PortConnectionRulesForNetsSimulation,
     AnInputNamingOnlyADataTypeIsANetReadingHighZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub(input logic a, output logic b);\n"
                       "  assign b = a;\n"
                       "endmodule\n"
                       "module t;\n"
                       "  logic b, e;\n"
                       "  tri0 n0;\n"
                       "  tri1 n1;\n"
                       "  wire nw;\n"
                       "  sub s(.b(b));\n"
                       "  sub s2(.a(), .b(e));\n"
                       "  initial #1 $display(\"unconnected=%b empty=%b "
                       "tri0=%b tri1=%b wire=%b\", b, e, n0, n1, nw);\n"
                       "endmodule\n",
                       f),
            "unconnected=z empty=z tri0=0 tri1=1 wire=z\n");
}

}  // namespace
