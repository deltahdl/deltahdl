#include "fixture_simulator.h"
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

// §10.3.3: the delay on a continuous assignment is a constant expression, which
// may be a parameter (§6.20) rather than a literal. The delay is not folded at
// elaboration; it is resolved at run time from the parameter's value -- a
// different evaluation path than a literal -- and still defers the assignment
// by that many time units. Built from real parameter-declaration source and
// driven through the full pipeline.
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

// §10.3.3: the same deferral holds when the delay's constant expression is a
// localparam (§6.20.2). A localparam reaches the simulator through a distinct
// declaration path than a module parameter but likewise resolves to the delay
// value that governs the assignment.
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
  // A.2.1.3 net_declaration: the packed range is part of data_type_or_implicit,
  // and delay3 follows it -- the legal order is `wire [7:0] #5 w`, not
  // `wire #5 [7:0] w`.
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] #5 w = 8'hAB;\n"
      "endmodule\n",
      f, "w");
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

// §10.3.3: "A delay given to a continuous assignment shall specify the time
// duration between a right-hand operand value change and the assignment made to
// the left-hand side", and §28.16 measures a net delay "from any driver on the
// net changing value to the time when the net value is updated and propagated
// further". Both operands of `a & b` change in one time step here, which every
// other delayed case in this file avoids by driving a one-operand or constant
// right-hand side, so this is the first case where the assignment has more than
// one operand change to react to at once. It fails when the second operand's
// change costs the assignment its delay and puts the new value on y at t=9
// rather than t=15: y_mid, sampled at t=11, then reads 8'h38 instead of the
// 8'hC0 y still holds.
//
// §4.7 leaves the order of active events within one region free, so neither
// sample stands at the change instant (t=9) or at the expiry instant (t=15).
// t=11 is strictly inside the delay and t=18 strictly after it, and no other
// event of this design stands at either time.
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
  // t=11: the operands changed at t=9 and the delay has not run out, so y still
  // carries 8'hF0 & 8'hCC.
  EXPECT_EQ(y_mid->value.ToUint64(), 0xC0u);
  // t=18: the delay ran out at t=15, so y carries 8'h3C & 8'h7A.
  EXPECT_EQ(y_late->value.ToUint64(), 0x38u);
}

// §10.3.3 again, with three operands changing in one time step rather than two.
// A second operand change is enough to strand one sibling of the assignment's
// change-watch; a third strands two, and the second stranded sibling drives the
// assignment through another evaluate-and-commit cycle. The extra commits carry
// the same right-hand side value (§10.3.2 evaluates the whole right-hand side,
// and all three operands already hold their new values when any of them is
// reacted to), so what separates one commit from several is when the new value
// reaches y and not what it is. This test therefore observes "committed once"
// as: y carries its old value at both samples strictly inside the delay, the
// new value at the sample strictly after it, and its value changes exactly once
// across that window -- an extra commit lands at the change instant t=9 and is
// read by the t=11 and t=14 samples, and a commit of any third value is read as
// a second change. A repeat commit of the identical value at the identical time
// is not observable through this fixture, and is not claimed.
//
// `changes` counts value changes of y, and §9.4.2 `@(y)` fires on a change
// rather than on every drive, so the difference between the count sampled at
// t=14 and the count sampled at t=25 is the number of new values y took over
// the delay window: one.
//
// §4.7 leaves the order of active events within one region free, so no sample
// stands at t=9 (the operand change), at t=15 (the expiry) or at t=6 (where y
// first settles). t=11 and t=14 are strictly inside the delay; t=18 and t=25
// are strictly after it.
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
  // t=11 and t=14: the operands changed at t=9 and the delay has not run out,
  // so y still carries 8'hF0 & 8'hCC & 8'hAA at both.
  EXPECT_EQ(y_early->value.ToUint64(), 0x80u);
  EXPECT_EQ(y_mid->value.ToUint64(), 0x80u);
  // t=18: the delay ran out at t=15, so y carries 8'h6E & 8'h7C & 8'hE7.
  EXPECT_EQ(y_late->value.ToUint64(), 0x64u);
  // Between t=14 and t=25 y took exactly one new value, at t=15.
  EXPECT_EQ(changes_late->value.ToUint64() - changes_mid->value.ToUint64(), 1u);
}

}  // namespace
