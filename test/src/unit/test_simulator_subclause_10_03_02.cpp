#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ContAssignStatementSim, NetDrivenByConstant) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  assign a = 8'hAB;\n"
      "endmodule\n",
      f, "a");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  assign wide = 16'hCAFE;\n"
      "endmodule\n",
      f, "wide");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §10.3.2: "Nets can be driven by multiple continuous assignments or by a
// mixture of primitive outputs, module outputs, and continuous assignments." A
// continuous assignment into a select of a net is one of those drivers, so the
// net has a driver to resolve rather than a value written into it behind
// resolution's back. A whole-identifier target cannot fail this.
TEST(ContAssignStatementSim, SelectTargetRegistersADriverOnTheNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [1:0] w;\n"
      "  assign w[0] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->drivers.size(), 1u);
}

// The driver drives only the bits the select names, and high impedance
// everywhere else, so §28.12 decides the rest of the net from its other
// sources. §6.6.5 gives a tri0 net "a continuous 0 of pull strength" wherever
// nothing overrides it, and that is what the undriven nibble resolves to: the
// low nibble is the assignment's strong 1 and the high nibble the net's own
// pull 0. Written into storage rather than resolved, the net would report the
// undriven answer for all eight bits.
TEST(ContAssignStatementSim, SelectTargetDrivesOnlyTheBitsItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] w;\n"
      "  assign w[3:0] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->BitStrength(0).s1_hi, Strength::kStrong);
  EXPECT_EQ(w->BitStrength(0).s0_hi, Strength::kHighz);
  EXPECT_EQ(w->BitStrength(4).s0_hi, Strength::kPull);
  EXPECT_EQ(w->BitStrength(4).s1_hi, Strength::kHighz);
}

// Two assignments into overlapping selects of one net are two drivers, and
// §28.12 combines them where they overlap: bits 1 and 2 are driven 1 by one and
// 0 by the other at the same strength, which resolves to x, while the bits only
// one of them names keep that one's value. A direct write into storage would
// leave whichever assignment ran last standing over the whole overlap.
TEST(ContAssignStatementSim, OverlappingSelectTargetsResolveAgainstEachOther) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  assign w[2:0] = 3'b111;\n"
      "  assign w[3:1] = 3'b000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->drivers.size(), 2u);
  EXPECT_EQ(w->resolved->value.ToString(), "0xx1");
}

}  // namespace
