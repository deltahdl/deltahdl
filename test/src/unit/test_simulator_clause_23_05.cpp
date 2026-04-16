#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- Req 1: Extern declaration shall not interfere with simulation ---

TEST(ExternModuleSimulation, ExternDoesNotInterfereWithSimulation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hAB;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// --- Req 2: .* port resolution from extern simulates correctly ---

TEST(ExternModuleSimulation, WildcardPortsFromExternSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'hCD;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

}  // namespace
