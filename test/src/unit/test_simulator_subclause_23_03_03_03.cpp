
#include <gtest/gtest.h>

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
  // An input net port accepts any expression, not just a bare signal; the
  // simulator evaluates the connection expression and drives the port with
  // its computed value.
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
  // An input net port accepts any compatible expression, including a constant
  // parameter reference. Built from a real parameter declaration and driven
  // end-to-end, the elaborated constant reaches the port and its sink.
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
  // A localparam constant is likewise carried across an input net port
  // connection to its sink when driven through the full pipeline.
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

// §23.3.3.3 connects an inout net port to a net, and §23.3.3.7 merges the
// port's net and the connected net into one simulated net, so a continuous
// assignment inside the child is one driver of the parent's net beside the
// parent's own, and §6.6.1's wire resolution combines the two: the parent
// drives the low nibble and leaves the high one at z, the child the reverse.
// Written directly into the shared variable rather than joining the drivers,
// the child's value would stand alone as 8'hFz or be overwritten by the
// parent's 8'hz0; only the resolved 8'hF0 says both drivers reached the net.
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

}  // namespace
