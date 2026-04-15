
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R1: continuous assignment implied when variable connected to input port;
//     if left unconnected, default initial value ---

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

// --- R2: continuous assignment implied when variable connected to output port
//     of an instance ---

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

// --- R5: ref port shall be connected to an equivalent variable data type;
//     references treated as hierarchical references ---

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

}  // namespace
