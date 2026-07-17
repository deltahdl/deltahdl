#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ContAssignStatementSim, NetDrivenByConstant) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  assign a = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ContAssignStatementSim, MultipleContinuousAssignments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd10;\n"
      "  assign b = a + 8'd1;\n"
      "  assign c = a + 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 12u);
}

TEST(ContAssignStatementSim, ContinuousAssignChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial a = 8'd7;\n"
      "  assign b = a;\n"
      "  assign c = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 7u);
}

TEST(ContAssignStatementSim, ReEvaluatesWhenOperandChanges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  assign b = a;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    #1;\n"
      "    a = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // The continuous assignment statement re-evaluates its RHS on every change of
  // an operand, so b tracks the latest value driven onto a rather than freezing
  // at the value present when simulation started.
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 42u);
}

TEST(ContAssignStatementSim, ContAssignOnVectorVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  assign wide = 16'hCAFE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// A continuous assignment may target a concatenation on the left-hand side —
// the form §10.3.2 uses to drive several nets that could not be assigned in a
// single net declaration. Each element receives its own most-significant-first
// slice of the whole right-hand value: for {hi, lo} = 8'hAB, hi takes the top
// nibble and lo the bottom nibble.
TEST(ContAssignStatementSim, ContAssignToConcatenationLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  assign {hi, lo} = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("hi")->value.ToUint64(), 0xAu);
  EXPECT_EQ(f.ctx.FindVariable("lo")->value.ToUint64(), 0xBu);
}

// The driven net of a continuous assignment can inherit an implicit declaration
// (§6.10) rather than being declared explicitly. Built from that real form —
// an undeclared left-hand name — the implicit net is created, driven, and
// carries the assigned value at the end of the run.
TEST(ContAssignStatementSim, ContAssignDrivesImplicitlyDeclaredNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
