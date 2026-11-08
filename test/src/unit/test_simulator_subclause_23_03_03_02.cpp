#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForVariablesSimulation,
     InputPortReceivesValueFromParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
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

TEST(PortConnectionRulesForVariablesSimulation,
     OutputPortDrivesParentVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output logic [7:0] y);\n"
      "  initial y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedInputVarTakesDataTypeDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(PortConnectionRulesForVariablesSimulation, RefPortWriteReflectsInParent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(ref logic [7:0] v);\n"
      "  initial v = 8'hAB;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] shared;\n"
      "  child u(shared);\n"
      "endmodule\n",
      f, "shared");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd7), .b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesNetPositional) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'h33;\n"
      "  logic [7:0] result;\n"
      "  child u(w, result);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedFourStateInputVarDefaultsToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedTwoStateInputVarDefaultsToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input var bit [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

TEST(RefPortSimulation, WritesOnEitherSideAreSeenOnTheOther) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(ref int r);\n"
                       "  initial begin\n"
                       "    #1 $display(\"child %0d\", r);\n"
                       "    #2 $display(\"child2 %0d\", r);\n"
                       "    r = r + 11;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  int v = 10;\n"
                       "  child c(.r(v));\n"
                       "  initial begin\n"
                       "    #2 v = 20;\n"
                       "    $display(\"parent %0d\", v);\n"
                       "    #2 $display(\"final %0d\", v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "child 10\nparent 20\nchild2 20\nfinal 31\n");
}

TEST(RefPortSimulation, RefPortBesideTheOtherDirections) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(input logic [7:0] a, b, output logic "
                       "[7:0] s, inout wire io, ref int r);\n"
                       "  assign s = a + b;\n"
                       "  assign io = 1'b1;\n"
                       "  initial #1 r = 42;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [7:0] s;\n"
                       "  wire io;\n"
                       "  int r = 0;\n"
                       "  child c(.a(8'd5), .b(8'd7), .s(s), .io(io), .r(r));\n"
                       "  initial #2 $display(\"sum %0d r %0d io %0d\", s, r, "
                       "io);\n"
                       "endmodule\n",
                       f),
            "sum 12 r 42 io 1\n");
}

TEST(GenerateBlockRefConnectionSim, ARefReachesTheVariableItsBlockDeclares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(ref logic [7:0] r);\n"
                       "  initial #1 r = 8'h5A;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  if (1) begin : g\n"
                       "    logic [7:0] v = 8'h00;\n"
                       "    child c(.r(v));\n"
                       "  end\n"
                       "  initial #2 $display(\"g.v %h\", g.v);\n"
                       "endmodule\n",
                       f),
            "g.v 5a\n");
}

TEST(GenerateBlockRefConnectionSim, TheBlocksVariableStandsOverTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(ref logic [7:0] r);\n"
                       "  initial #1 r = 8'h5A;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [7:0] v = 8'hC3;\n"
                       "  if (1) begin : g\n"
                       "    logic [7:0] v = 8'h00;\n"
                       "    child c(.r(v));\n"
                       "  end\n"
                       "  initial #2 $display(\"g.v %h v %h\", g.v, v);\n"
                       "endmodule\n",
                       f),
            "g.v 5a v c3\n");
}

}  // namespace
