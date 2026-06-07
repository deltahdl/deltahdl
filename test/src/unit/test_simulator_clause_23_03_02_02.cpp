
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NamedPortSimulation, NamedInputPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'hAB), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NamedPortSimulation, NamedPortExpressionEvaluated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'hF0 | 8'h0F), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(NamedPortSimulation, ReversedOrderProducesCorrectResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result), .a(8'h42));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x42u);
}

TEST(NamedPortSimulation, EmptyNamedOutputNotDriven) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] a, output logic [7:0] b);\n"
      "  assign a = 8'hAA;\n"
      "  assign b = 8'hBB;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(), .b(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBu);
}

TEST(NamedPortSimulation, OmittedInputUsesDefaultValueAtRuntime) {
  // §23.3.2.2: an input port left out of a named connection list falls back to
  // its declared default. b is omitted here, so the child evaluates a + b using
  // b's default of 5; the parent observing 10 + 5 confirms the default was both
  // substituted during elaboration and actually drove the simulated logic --
  // the runtime counterpart to the elaborator's binding-level observation.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'd5,\n"
      "             output logic [7:0] c);\n"
      "  assign c = a + b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.a(8'd10), .c(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

}
