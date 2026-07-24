#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

// §23.5 end-to-end via the §23.2.2 non-ANSI port dependency: the extern is
// non-ANSI (port names only), `.*` brings those names onto the module, and the
// module body supplies the directions with non-ANSI port declarations. Build
// the whole thing from real syntax and drive it to runtime, observing the
// combinational result of the extern-derived ports.
TEST(ExternModuleSimulation, NonAnsiExternWildcardSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "extern module gate(a, b, c, d);\n"
      "module gate(.*);\n"
      "  input a, b, c;\n"
      "  output d;\n"
      "  assign d = a & b & c;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c, d;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b1;\n"
      "  assign c = 1'b1;\n"
      "  gate u0(.a(a), .b(b), .c(c), .d(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §23.5 end-to-end via the §23.2.3 parameterized-module dependency: the extern
// carries a value parameter that sizes its ports; `.*` places that parameter
// and those ports on the module. Simulate and observe the full parameterized
// width.
TEST(ExternModuleSimulation, ValueParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "extern module widen #(parameter W = 4)\n"
      "  (input logic [W-1:0] a, output logic [W-1:0] b);\n"
      "module widen(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] a, b;\n"
      "  assign a = 4'hA;\n"
      "  widen u0(.a(a), .b(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// §23.5 end-to-end via the §23.2.3 dependency in its type-parameter form (a
// distinct code path from a value parameter): a type parameter sizes the
// extern's ports and `.*` imports it. Observe the byte-wide result at run time.
TEST(ExternModuleSimulation, TypeParameterizedExternWildcardSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "extern module conv #(parameter type TP = logic [7:0])\n"
      "  (input TP a, output TP b);\n"
      "module conv(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = 8'h5A;\n"
      "  conv u0(.a(a), .b(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

// §23.5 end-to-end via the §23.4 nested-module dependency: an extern module
// declaration nested inside another module's body coexists with the actual
// nested definition and does not disturb simulation of the instantiated child.
TEST(ExternModuleSimulation, NestedExternModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  module child(input logic [7:0] a, output logic [7:0] b);\n"
      "    assign b = a;\n"
      "  endmodule\n"
      "  assign a = 8'h3C;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3Cu);
}

}  // namespace
