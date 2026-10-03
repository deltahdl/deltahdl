
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NamedPortSimulation, NamedInputPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'hAB), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NamedPortSimulation, NamedPortExpressionEvaluated) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'hF0 | 8'h0F), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(NamedPortSimulation, ReversedOrderProducesCorrectResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result), .a(8'h42));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(NamedPortSimulation, EmptyNamedOutputNotDriven) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] a, output logic [7:0] b);\n"
      "  assign a = 8'hAA;\n"
      "  assign b = 8'hBB;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBu);
}

TEST(NamedPortSimulation, ExplicitEmptyNamedInputDiscardsDefaultAtRuntime) {
  // §23.3.2.2: an input port that carries a default value but is given an
  // explicit empty named connection ".a()" is left unconnected, and its default
  // is deliberately NOT substituted -- the opposite of merely omitting the port
  // from the list (OmittedInputUsesDefaultValueAtRuntime), which does fall back
  // to the default. Here b's default of 5 must be discarded, so the child's
  // unconnected input propagates an unknown value rather than 15; observing the
  // result as not-known is the runtime counterpart to the elaborator's
  // binding-level check that the connection is 'z, confirming the default was
  // not driven into the simulated logic.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'd5,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd10), .b(), .c(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(NamedPortSimulation, OmittedInputUsesDefaultValueAtRuntime) {
  // §23.3.2.2: an input port left out of a named connection list falls back to
  // its declared default. b is omitted here, so the child evaluates a + b using
  // b's default of 5; the parent observing 10 + 5 confirms the default was both
  // substituted during elaboration and actually drove the simulated logic --
  // the runtime counterpart to the elaborator's binding-level observation.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'd5,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd10), .c(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §23.3.2.2 (printed page 743): a named connection `.dout(d3)` connects the
// port to the parent's `d3` and to nothing else, and §23.9 (printed page 761)
// keeps the child's bare `dout` inside the child, so a parent net that shares
// the port's name plays no part: the child's value reaches d3 and the parent's
// own `dout`, which nothing drives, reads z. An `output logic` port is a
// variable rather than a net under the child's prefix, and the child's
// `assign dout` found no net there, stepped out to the parent's like-named one
// and drove it, leaving d3 x.
TEST(PortConnectionSim, OutputVariablePortDrivesOnlyTheConnectedNet) {
  SimFixture f;
  auto out = RunCapture(
      "module xt3(output logic [3:0] dout, input din);\n"
      "  assign dout = {3'b100, din};\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] dout, d3;\n"
      "  xt3 z(.dout(d3), .din(1'b1));\n"
      "  initial #1 $display(\"dout %b d3 %b\", dout, d3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "dout zzzz d3 1001\n");
}

// The same for an output net port, and for a parent net that shares the port's
// name and is connected to it by name, `.y(y)`: the child's value reaches the
// connected net whichever name it has.
TEST(PortConnectionSim, OutputNetPortDrivesOnlyTheConnectedNet) {
  SimFixture f;
  auto out = RunCapture(
      "module xt3(output [3:0] dout, input din);\n"
      "  assign dout = {3'b100, din};\n"
      "endmodule\n"
      "module r1(input [7:0] x, output [7:0] y);\n"
      "  assign y = x * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] dout, d3;\n"
      "  wire [7:0] y;\n"
      "  assign dout = 4'b0110;\n"
      "  xt3 z(.dout(d3), .din(1'b1));\n"
      "  r1 i(.x(8'd100), .y(y));\n"
      "  initial #1 $display(\"dout %b d3 %b y %0d\", dout, d3, y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "dout 0110 d3 1001 y 200\n");
}

}  // namespace
