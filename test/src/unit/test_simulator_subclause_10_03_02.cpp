#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
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

TEST(ContAssignStatementSim, SelectTargetRunningOffLowEndDrivesItsOwnHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[1 -: 4] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0x03u);
}

TEST(ContAssignStatementSim,
     SelectTargetRunningOffLowEndLeavesTheOtherBitsUndriven) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] a;\n"
      "  assign a[1 -: 4] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToString(), "zzzzzz11");
}

TEST(ContAssignStatementSim,
     SelectTargetRunningOffHighEndStillTakesItsLowBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[9:6] = 4'b1101;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0x40u);
}

TEST(ContAssignStatementSim, SelectTargetRunningOffBothEndsLandsItsMiddleBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [7:0] a;\n"
      "  assign a[9 -: 12] = 12'hABC;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->resolved->value.ToUint64() & 0xFFu, 0xAFu);
}

TEST(ContAssignStatementSim, ConcatTargetRegistersADriverOnEachNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire carry_out, carry_in;\n"
      "  wire [3:0] sum_out, ina, inb;\n"
      "  assign ina = 4'd9;\n"
      "  assign inb = 4'd8;\n"
      "  assign carry_in = 1'b1;\n"
      "  assign {carry_out, sum_out} = ina + inb + carry_in;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* carry_out = f.ctx.FindNet("carry_out");
  auto* sum_out = f.ctx.FindNet("sum_out");
  ASSERT_NE(carry_out, nullptr);
  ASSERT_NE(sum_out, nullptr);
  EXPECT_EQ(carry_out->drivers.size(), 1u);
  EXPECT_EQ(sum_out->drivers.size(), 1u);
  EXPECT_EQ(sum_out->resolved->value.ToUint64(), 2u);
}

TEST(ContAssignStatementSim, ConcatTargetLeavesTheRestOfANetToResolution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 [3:0] a;\n"
      "  wire b;\n"
      "  assign {b, a[1:0]} = 3'b111;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->drivers.size(), 1u);
  EXPECT_EQ(a->resolved->value.ToString(), "0011");
}

TEST(ContAssignStatementSim, ConcatTargetNamingOneNetTwiceTakesTwoSlots) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] a;\n"
      "  assign {a[3:2], a[1:0]} = 4'ha;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindNet("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->drivers.size(), 2u);
  EXPECT_EQ(a->resolved->value.ToUint64(), 0xAu);
}

TEST(ContAssignStatementSim, ConcatTargetEvaluatesTheRhsAtTheWholeTargetWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire carry_out, carry_in;\n"
      "  wire [3:0] sum_out, ina, inb;\n"
      "  assign ina = 4'd9;\n"
      "  assign inb = 4'd8;\n"
      "  assign carry_in = 1'b1;\n"
      "  assign {carry_out, sum_out} = ina + inb + carry_in;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* carry_out = f.ctx.FindVariable("carry_out");
  auto* sum_out = f.ctx.FindVariable("sum_out");
  ASSERT_NE(carry_out, nullptr);
  ASSERT_NE(sum_out, nullptr);
  EXPECT_EQ(carry_out->value.ToUint64(), 1u);
  EXPECT_EQ(sum_out->value.ToUint64(), 2u);
}

TEST(ContAssignStatementSim, NestedConcatTargetEvaluatesAtTheOutermostWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire carry_out, carry_in;\n"
      "  wire [1:0] sum_hi, sum_lo;\n"
      "  wire [3:0] ina, inb;\n"
      "  assign ina = 4'd9;\n"
      "  assign inb = 4'd8;\n"
      "  assign carry_in = 1'b1;\n"
      "  assign {carry_out, {sum_hi, sum_lo}} = ina + inb + carry_in;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* carry_out = f.ctx.FindVariable("carry_out");
  auto* sum_hi = f.ctx.FindVariable("sum_hi");
  auto* sum_lo = f.ctx.FindVariable("sum_lo");
  ASSERT_NE(carry_out, nullptr);
  ASSERT_NE(sum_hi, nullptr);
  ASSERT_NE(sum_lo, nullptr);
  EXPECT_EQ(carry_out->value.ToUint64(), 1u);
  EXPECT_EQ(sum_hi->value.ToUint64(), 0u);
  EXPECT_EQ(sum_lo->value.ToUint64(), 2u);
}

TEST(ContAssignStatementSim, ConcatTargetSignExtendsASignedRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire signed [3:0] a;\n"
      "  wire c;\n"
      "  wire [3:0] s;\n"
      "  assign a = -4'sd1;\n"
      "  assign {c, s} = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* c = f.ctx.FindVariable("c");
  auto* sv = f.ctx.FindVariable("s");
  ASSERT_NE(c, nullptr);
  ASSERT_NE(sv, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
  EXPECT_EQ(sv->value.ToUint64(), 0xFu);
}

TEST(ContAssignStatementSim, ConcatTargetFollowsItsOperandsAfterTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  wire carry_out;\n"
      "  wire [3:0] sum_out;\n"
      "  logic [3:0] ina, inb;\n"
      "  logic carry_in;\n"
      "  assign {carry_out, sum_out} = ina + inb + carry_in;\n"
      "  initial begin\n"
      "    ina = 4'd9; inb = 4'd8; carry_in = 1'b1;\n"
      "    #1 $display(\"%b %b\", carry_out, sum_out);\n"
      "    ina = 4'd1; inb = 4'd2; carry_in = 1'b0;\n"
      "    #1 $display(\"%b %b\", carry_out, sum_out);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0010\n0 0011\n");
}

TEST(ContAssignSim, ReEvaluatedWhenAStaticClassPropertyItReadsChanges) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C; static int s = 60; endclass\n"
      "  wire [31:0] w;\n"
      "  int result;\n"
      "  assign w = C::s + 1;\n"
      "  initial begin\n"
      "    #1 C::s = 61;\n"
      "    #1 result = w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 62u);
}

TEST(ContAssignSim, ReEvaluatedWhenAPackageVariableItReadsChanges) {
  auto v = RunAndGet(
      "package p;\n"
      "  int g = 70;\n"
      "endpackage\n"
      "module t;\n"
      "  wire [31:0] w;\n"
      "  int result;\n"
      "  assign w = p::g + 1;\n"
      "  initial begin\n"
      "    #1 p::g = 5;\n"
      "    #1 result = w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(ContAssignStatementSim, AnUnchangedRhsValueGivesTheTargetNoEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a = 0, b = 0; int n = 0;\n"
                       "  wire w;\n"
                       "  assign w = a & b;\n"
                       "  always @(w) if ($time > 0) n++;\n"
                       "  initial begin\n"
                       "    #1 a = 1; #1 a = 0; #1 b = 1;\n"
                       "    #1 $display(\"%0d %b\", n, w);\n"
                       "    a = 1;\n"
                       "    #1 $display(\"%0d %b\", n, w);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 0\n1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
