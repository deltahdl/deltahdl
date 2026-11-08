#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentDelaySim, SingleDelayDefersAssignment) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #10 y = 8'hAB;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, ParameterValuedDelayDefersAssignment) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter D = 10;\n"
      "  wire [7:0] y;\n"
      "  assign #D y = 8'hAB;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, LocalparamValuedDelayDefersAssignment) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam D = 7;\n"
      "  wire [7:0] y;\n"
      "  assign #D y = 8'h5C;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Cu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesRiseForZeroToOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = 1'b1;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesFallForOneToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #20 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 30u);
}

TEST(AssignmentDelaySim, ThreeDelayTurnoff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #(5, 10, 15) y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #20 src = 1'bz;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 35u);
}

TEST(AssignmentDelaySim, NoDelayAssignsImmediately) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign y = 8'd99;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(AssignmentDelaySim, TwoDelayVectorXToKnownUsesRise) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = 8'hFF;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 20u);
}

TEST(AssignmentDelaySim, VectorNonzeroToNonzeroUsesRise) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h01;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 70u);
}

TEST(AssignmentDelaySim, VectorNonzeroToZeroUsesFall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 55u);
}

TEST(AssignmentDelaySim, WideVectorNonzeroAboveTheFirstWordToZeroUsesFall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [127:0] src;\n"
      "  wire [127:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 128'h1 << 100;\n"
      "    #50 src = '0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 55u);
}

TEST(AssignmentDelaySim, VectorTransitionToZUsesTurnoff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5, 8) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'hzz;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 58u);
}

TEST(AssignmentDelaySim, NetDeclSingleDelayApplied) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire #10 w = 1'b1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, VectorNetDeclDelayWholeVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] #5 w = 8'hAB;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(AssignmentDelaySim, VectorNetDeclMultiDelayUsesFallForNonzeroToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] #(20, 5) w = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 55u);
}

TEST(AssignmentDelaySim, ANetDelaySettlesAVectorWholeWhenItsBitsDisagree) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] src;\n"
      "  wire [1:0] #(2, 4) w;\n"
      "  assign w = src;\n"
      "  initial begin\n"
      "    src = 2'b01;\n"
      "    #50 src = 2'b10;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 52u);
}

TEST(AssignmentDelaySim, ADeclarationAssignmentSettlesTheSameVectorWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] src;\n"
      "  wire [1:0] #(2, 4) w = src;\n"
      "  initial begin\n"
      "    src = 2'b01;\n"
      "    #50 src = 2'b10;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 52u);
}

TEST(AssignmentDelaySim, ANetDelayUsesTheFallingDelayForNonzeroToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] src;\n"
      "  wire [1:0] #(2, 4) w;\n"
      "  assign w = src;\n"
      "  initial begin\n"
      "    src = 2'b11;\n"
      "    #50 src = 2'b00;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 54u);
}

TEST(AssignmentDelaySim, SingleDelayAppliedToNettypeNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  nettype logic nt;\n"
      "  nt n;\n"
      "  assign #10 n = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* net = f.ctx.FindNet("n");
  ASSERT_NE(net, nullptr);
  ASSERT_TRUE(net->is_user_nettype);
  ASSERT_NE(net->resolved, nullptr);
  EXPECT_EQ(net->resolved->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, InertialDelayCancelsPending) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 15u);
}

TEST(AssignmentDelaySim, InertialReturnToCurrentValueSchedulesNoEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    src = 1'b0;\n"
      "    #20 src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 25u);
}

TEST(AssignmentDelaySim, InertialDelayNoIntermediateGlitch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  logic [7:0] count;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "    #20 count = count;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AssignmentDelaySim, TwoOperandsChangingInOneStepStillWaitTheDelay) {
  SimFixture f;
  auto* y_mid = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  wire [7:0] y;\n"
      "  logic [7:0] y_mid;\n"
      "  logic [7:0] y_late;\n"
      "  assign #6 y = a & b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'hCC;\n"
      "    #9;\n"
      "    a = 8'h3C;\n"
      "    b = 8'h7A;\n"
      "    #2 y_mid = y;\n"
      "    #7 y_late = y;\n"
      "  end\n"
      "endmodule\n",
      f, "y_mid");
  ASSERT_NE(y_mid, nullptr);
  auto* y_late = f.ctx.FindVariable("y_late");
  ASSERT_NE(y_late, nullptr);
  EXPECT_EQ(y_mid->value.ToUint64(), 0xC0u);
  EXPECT_EQ(y_late->value.ToUint64(), 0x38u);
}

TEST(AssignmentDelaySim, ThreeOperandsChangingInOneStepCommitOnce) {
  SimFixture f;
  auto* y_early = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] c;\n"
      "  wire [7:0] y;\n"
      "  logic [7:0] changes;\n"
      "  logic [7:0] y_early;\n"
      "  logic [7:0] y_mid;\n"
      "  logic [7:0] y_late;\n"
      "  logic [7:0] changes_mid;\n"
      "  logic [7:0] changes_late;\n"
      "  assign #6 y = a & b & c;\n"
      "  always @(y) changes = changes + 1;\n"
      "  initial begin\n"
      "    changes = 0;\n"
      "    a = 8'hF0;\n"
      "    b = 8'hCC;\n"
      "    c = 8'hAA;\n"
      "    #9;\n"
      "    a = 8'h6E;\n"
      "    b = 8'h7C;\n"
      "    c = 8'hE7;\n"
      "    #2 y_early = y;\n"
      "    #3;\n"
      "    y_mid = y;\n"
      "    changes_mid = changes;\n"
      "    #4 y_late = y;\n"
      "    #7 changes_late = changes;\n"
      "  end\n"
      "endmodule\n",
      f, "y_early");
  ASSERT_NE(y_early, nullptr);
  auto* y_mid = f.ctx.FindVariable("y_mid");
  ASSERT_NE(y_mid, nullptr);
  auto* y_late = f.ctx.FindVariable("y_late");
  ASSERT_NE(y_late, nullptr);
  auto* changes_mid = f.ctx.FindVariable("changes_mid");
  ASSERT_NE(changes_mid, nullptr);
  auto* changes_late = f.ctx.FindVariable("changes_late");
  ASSERT_NE(changes_late, nullptr);
  EXPECT_EQ(y_early->value.ToUint64(), 0x80u);
  EXPECT_EQ(y_mid->value.ToUint64(), 0x80u);
  EXPECT_EQ(y_late->value.ToUint64(), 0x64u);
  EXPECT_EQ(changes_late->value.ToUint64() - changes_mid->value.ToUint64(), 1u);
}

TEST(AssignmentDelaySim, SelectOffTheLowEndFallsOnTheBitsThatLand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] src;\n"
      "  tri [7:0] a;\n"
      "  assign #(2, 3) a[1 -: 4] = src;\n"
      "  initial begin\n"
      "    src = 4'b1111;\n"
      "    #20 src = 4'b0011;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "zzzzzz00");
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 23u);
}

TEST(AssignmentDelaySim, OneBitDrivenWindowTakesTheScalarTransitionTable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:0] s;\n"
      "  tri [7:0] b;\n"
      "  assign #(2, 3) b[0 -: 2] = s;\n"
      "  initial s = 2'b01;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "zzzzzzz0");
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 3u);
}

TEST(AssignmentDelaySim, ANetDelayDelaysAnOutputPortDriver) {
  const char* src =
      "module c(output logic o);\n"
      "  initial begin o = 1'b0; #1 o = 1'b1; end\n"
      "endmodule\n"
      "module t;\n"
      "  wire #10 x;\n"
      "  logic r5, r12;\n"
      "  c u(.o(x));\n"
      "  initial begin #5 r5 = (x === 1'b1); #7 r12 = (x === 1'b1); end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r5"), 0u);
  EXPECT_EQ(RunAndGet(src, "r12"), 1u);
}

TEST(AssignmentDelaySim, NetDelayAppliesToDriverOfSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a = 0;\n"
      "  wire [1:0] #10 w;\n"
      "  assign w[0] = a;\n"
      "  initial #1 a = 1;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 11u);
}

TEST(AssignmentDelaySim, ConcatenationTargetSettlesTogether) {
  const char* src =
      "module t;\n"
      "  wire [3:0] a, b; wire p, q;\n"
      "  logic [7:0] r = 8'h01; logic [1:0] s = 2'b01;\n"
      "  assign #(5, 10) {a, b} = r;\n"
      "  assign #(5, 10) {p, q} = s;\n"
      "  logic [7:0] v; logic [1:0] w;\n"
      "  initial begin\n"
      "    #20 begin r = 8'h10; s = 2'b10; end\n"
      "    #6 begin v = {a, b}; w = {p, q}; end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "v"), 0x10u);
  EXPECT_EQ(RunAndGet(src, "w"), 2u);
}

}  // namespace
