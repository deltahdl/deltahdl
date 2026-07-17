#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentDelaySim, SingleDelayDefersAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #10 y = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

// §10.3.3: the delay on a continuous assignment is a constant expression, which
// may be a parameter (§6.20) rather than a literal. The delay is not folded at
// elaboration; it is resolved at run time from the parameter's value -- a
// different evaluation path than a literal -- and still defers the assignment
// by that many time units. Built from real parameter-declaration source and
// driven through the full pipeline.
TEST(AssignmentDelaySim, ParameterValuedDelayDefersAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter D = 10;\n"
      "  wire [7:0] y;\n"
      "  assign #D y = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

// §10.3.3: the same deferral holds when the delay's constant expression is a
// localparam (§6.20.2). A localparam reaches the simulator through a distinct
// declaration path than a module parameter but likewise resolves to the delay
// value that governs the assignment.
TEST(AssignmentDelaySim, LocalparamValuedDelayDefersAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam D = 7;\n"
      "  wire [7:0] y;\n"
      "  assign #D y = 8'h5C;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5Cu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesRiseForZeroToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

TEST(AssignmentDelaySim, RiseFallDelayUsesFallForOneToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #(5, 10) y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #20 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign y = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(AssignmentDelaySim, TwoDelayVectorXToKnownUsesRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 20u);
}

TEST(AssignmentDelaySim, VectorNonzeroToNonzeroUsesRise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h01;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x01u);

  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 70u);
}

TEST(AssignmentDelaySim, VectorNonzeroToZeroUsesFall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] y;\n"
      "  assign #(20, 5) y = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
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
  // The vector drives all-z, so the turn-off (third) delay of 8 governs the
  // assignment rather than the rise (20) or fall (5) delay: 50 + 8 == 58.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 58u);
}

TEST(AssignmentDelaySim, NetDeclSingleDelayApplied) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire #10 w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, VectorNetDeclDelayWholeVector) {
  SimFixture f;
  // A.2.1.3 net_declaration: the packed range is part of data_type_or_implicit,
  // and delay3 follows it -- the legal order is `wire [7:0] #5 w`, not
  // `wire #5 [7:0] w`.
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] #5 w = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 5u);
}

// §10.3.3: when a continuous assignment carrying multiple delays is part of a
// vector net's declaration, the delay is selected for the whole vector -- the
// rising and falling delays are not applied to the individual bits. Built from
// real net-declaration syntax (§10.3.1) so the assignment genuinely lives in
// the declaration: a whole-vector transition from nonzero to zero picks the
// fall delay (5), landing the update at t=55 rather than the rise delay's t=70.
TEST(AssignmentDelaySim, VectorNetDeclMultiDelayUsesFallForNonzeroToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire [7:0] #(20, 5) w = src;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    #50 src = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 55u);
}

// §10.3.3: a continuous assignment to a net of a user-defined nettype admits
// only a single delay, and that one delay governs the assignment for any value
// change (there is no rise/fall/turn-off split, unlike a scalar or vector net).
// Built from real §6.7.2 nettype syntax and driven through the full pipeline:
// the delayed driver is committed by the production continuous-assignment delay
// path (SelectContAssignDelay returns the sole delay when no fall delay exists)
// and lands on the resolved net value only after the delay elapses.
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
  // The value change is deferred by the single delay: it is present only at
  // t=10, confirming the one delay was applied to the nettype net.
  EXPECT_EQ(net->resolved->value.ToUint64(), 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 10u);
}

TEST(AssignmentDelaySim, InertialDelayCancelsPending) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic src;\n"
      "  wire y;\n"
      "  assign #10 y = src;\n"
      "  initial begin\n"
      "    src = 1'b1;\n"
      "    #5 src = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 15u);
}

TEST(AssignmentDelaySim, InertialReturnToCurrentValueSchedulesNoEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  // y settles to 0 early, then the operand pulses high at t20 (scheduling a
  // y=1 event for t30) and returns to 0 at t25 before that event fires. Since
  // the re-evaluated right-hand side again equals the current left-hand side
  // value, the pending event is dropped and none is rescheduled, so the run
  // stops at t25 rather than advancing to the cancelled event time of 35.
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 25u);
}

TEST(AssignmentDelaySim, InertialDelayNoIntermediateGlitch) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
