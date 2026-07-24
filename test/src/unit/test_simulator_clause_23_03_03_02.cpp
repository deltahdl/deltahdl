
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionRulesForVariablesSimulation,
     InputPortReceivesValueFromParent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] drv = 8'h42;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(drv), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     OutputPortDrivesParentVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] y);\n"
      "  initial y = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.y(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x55u);
}

TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedInputVarTakesDataTypeDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // The input is a variable left unconnected, so it holds the default initial
  // value of its data type. For 4-state logic that default is x, which the
  // child forwards to result -- distinct from the high-Z an unconnected net
  // input would carry.
  EXPECT_EQ(var->value.ToString(), "xxxxxxxx");
}

TEST(PortConnectionRulesForVariablesSimulation, RefPortWriteReflectsInParent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(ref logic [7:0] v);\n"
      "  initial v = 8'hAB;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] shared;\n"
      "  child u(shared);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("shared");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// R1a admits any compatible expression on a variable input port, including a
// constant literal. The implied continuous assignment carries the literal into
// the port, and the child forwards it out, so the parent observes the constant.
TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd7), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// R1a on a variable input port also admits a net operand, connected here by
// ordered (positional) list rather than by name. The net's value flows through
// the implied continuous assignment into the variable input port -- a net-to-
// variable connection whose compatibility is the §6.22.3 dependency in action.
TEST(PortConnectionRulesForVariablesSimulation,
     VariableInputPortReceivesNetPositional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input var logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  assign w = 8'h33;\n"
      "  logic [7:0] result;\n"
      "  child u(w, result);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
}

// R1d: an unconnected variable input port takes the default initial value of
// its data type. For a 2-state type that default is 0, distinct from the x an
// unconnected 4-state variable input carries. This observes the data-type-
// dependent branch of the default rather than repeating the 4-state case.
TEST(PortConnectionRulesForVariablesSimulation,
     UnconnectedTwoStateInputVarDefaultsToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input var bit [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "00000000");
}

}  // namespace
