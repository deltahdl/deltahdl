#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/awaiters.h"
#include "simulator/clocking.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EventControlSim, EventControlPosedge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, EventControlNegedge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, EventControlAnyChange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 8'd0;\n"
      "    #5 sig = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    @(sig) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, SequentialPosedgeThenNegedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    @(posedge clk) a = 8'd1;\n"
      "    @(negedge clk) b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
}

TEST(EventControlSim, EdgeEventFiresOnPosedge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 0;\n"
      "    #5 sig = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge sig) x = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(EventControlSim, EdgeEventFiresOnNegedge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 1;\n"
      "    #5 sig = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge sig) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(EventControlSim, NoEventOnSameValueWrite) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 8'd5;\n"
      "    #5 sig = 8'd5;\n"
      "    #5 sig = 8'd7;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(sig) x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2 (printed page 232) closes with the rule this case holds the simulator
// to: "A change of value in any operand of the expression without a change in
// the result of the expression shall not be detected as an event." A write that
// deposits the value the variable already holds changes no operand's value, so
// `@(sig)` shall not resume on it.
//
// This is the discriminating replacement for NoEventOnSameValueWrite above,
// which offers the same three writes but reads a variable the waiting process
// sets to one constant. That variable reads 1 whether the event control fired
// on the same-value write or waited for the real change that follows it, so the
// assertion holds of a simulator that obeys the rule and of one that ignores
// it. Counting the resumptions is what tells the two apart: an event control
// that resumes on every notification of a write reaches 3, and one that
// compares the value it was given against the value it holds reaches 2.
//
// The count is 2 rather than 1 because the always procedure arms before the
// first write reaches it. Lowerer::LowerProcesses lowers every non-initial
// process ahead of the initial ones, and an Active region queue is first-in
// first-out, so `always @(sig)` has captured its baseline x before the initial
// block runs. The x-to-5 write at time 0 is the first resumption and the 5-to-7
// write at time 2 is the second; the 5-to-5 write at time 1 is the one the rule
// excludes. `woke` counts from zero without being assigned one, because it is
// 2-state and Table 6-7 gives such a variable a default of '0.
//
// It also blocks a regression that the always_comb cases for #3523 cannot see.
// That issue is that AnyChangeAwaiter re-runs an always_comb on a same-value
// write, and dropping the NotifyWatchers calls from WriteVar and
// AssignToScalarLhs would bring the always_comb counts out right while `@(sig)`
// stopped firing at all. This case counts what an event control does with those
// same notifications, so that cure fails it.
TEST(EventControlSim, SameValueWriteWakesNoEventControlCountedByEvaluations) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sig;\n"
      "  int woke;\n"
      "  always @(sig) woke = woke + 1;\n"
      "  initial begin\n"
      "    sig = 8'd5;\n"
      "    #1 sig = 8'd5;\n"
      "    #1 sig = 8'd7;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EventControlSim, PosedgeFiresOnZeroToZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(EventControlSim, PosedgeFiresOnZToOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(EventControlSim, NegedgeFiresOnOneToZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, NegedgeFiresOnZToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd88;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(EventControlSim, PosedgeFiresOnZeroToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EventControlSim, PosedgeFiresOnXToOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(EventControlSim, NegedgeFiresOnOneToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, NegedgeFiresOnXToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(EventControlSim, NoPosedgeOnXToZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoPosedgeOnZToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoNegedgeOnXToZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(negedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoNegedgeOnZToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(negedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, CompoundExprResultChangeFiresEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 0; b = 0;\n"
      "    x = 8'd0;\n"
      "    #5 a = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(a | b) x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, ChandleSameValueWriteIsNotEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  chandle h;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 h = null;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(h) x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, CompoundExprOperandChangeWithoutResultChangeIsNotEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 1; b = 1;\n"
      "    x = 8'd0;\n"
      "    #5 a = 0;\n"
      "    #5 b = 0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    @(a | b) x = 8'd99;\n"
      "    @(a | b) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, ObjectHandleChangeFiresEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "  endclass\n"
      "  C h;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    h = null;\n"
      "    #5 h = new();\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(h) x = 8'd77;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, DynamicArraySizeChangeReevaluatesEventExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 q.push_back(42);\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(q.size()) x = 8'd88;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(EventControlSim, NoEdgeOnXToZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(edge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoEdgeOnZToX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(edge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, EdgeFiresOnXToOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge clk) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, EdgeFiresOnZToZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge clk) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(EventControlSim, ClockingBlockInputResolvesThroughClockingManager) {
  SimFixture f;

  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  f.ctx.SetClockingManager(&cmgr);

  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kMemberAccess;
  member->lhs = f.arena.Create<Expr>();
  member->lhs->kind = ExprKind::kIdentifier;
  member->lhs->text = "cb";
  member->rhs = f.arena.Create<Expr>();
  member->rhs->kind = ExprKind::kIdentifier;
  member->rhs->text = "data";

  auto* wait_stmt = f.arena.Create<Stmt>();
  wait_stmt->kind = StmtKind::kEventControl;
  EventExpr ev;
  ev.edge = Edge::kNone;
  ev.signal = member;
  wait_stmt->events.push_back(ev);
  auto* null_body = f.arena.Create<Stmt>();
  null_body->kind = StmtKind::kNull;
  wait_stmt->body = null_body;

  EXPECT_EQ(data->watchers.size(), 0u);

  DriverResult result;
  auto coro = DriverCoroutine(wait_stmt, f.ctx, f.arena, &result);
  coro.Resume();

  EXPECT_EQ(data->watchers.size(), 1u);
}

// The "edge event ... only on the LSB" rule discriminated: an upper bit
// toggles while the LSB is held constant, so a posedge must NOT fire. A
// broken any-bit implementation would resume and write x.
TEST(EventControlSim, PosedgeIgnoresUpperBitChangeWhenLsbHeld) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd1;\n"
      "    x = 8'd0;\n"
      "    #5 wide = 8'd3;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(posedge wide) x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NegedgeIgnoresUpperBitChangeWhenLsbHeld) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd3;\n"
      "    x = 8'd0;\n"
      "    #5 wide = 8'd1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(negedge wide) x = 8'd55;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, EdgeIgnoresUpperBitChangeWhenLsbHeld) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd0;\n"
      "    x = 8'd0;\n"
      "    #5 wide = 8'd2;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(edge wide) x = 8'd66;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NamedEventTriggerReleasesWaiter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int hit;\n"
      "  initial begin\n"
      "    hit = 0;\n"
      "    fork\n"
      "      begin @e; hit = 1; end\n"
      "      begin #1 ->e; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2 admits any expression as an event_expression and puts no condition on
// the names in it, so a hierarchical name stands in one exactly as a local name
// does. A compound event over two of them armed watchers on nothing:
// CollectExprIdentifiers descended a member access as though it were an
// operator, collecting `u` and `a` from `u.a` as two bare names, and neither
// names anything in the instance the event is written in.
//
// Both operands are driven, and the process writes `hit` when it resumes, so a
// process that never resumes leaves the 0 it was initialised with.
TEST(EventControlSim, CompoundEventOverHierarchicalNamesResumes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic a, b;\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "  int hit;\n"
      "  initial begin\n"
      "    hit = 0;\n"
      "    fork\n"
      "      begin @(u.a & u.b) hit = 1; end\n"
      "      begin #1 u.a = 1'b1; u.b = 1'b1; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// The pair that isolates the disagreement, over one signal: `@(u.a)` goes to
// ResolveSignalToVariable, which flattens the name, and `@(u.a & 1'b1)` went to
// the collector, which shredded it. The first passed before this change and the
// second did not, and only the pair says the two paths have to agree about what
// one name denotes. Both counters are asserted, so a fix that broke the direct
// path to mend the compound one would not pass.
TEST(EventControlSim, TheDirectAndCompoundPathsAgreeOnAHierarchicalName) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic a;\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "  int hits;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    fork\n"
      "      begin @(u.a) hits = hits + 1; end\n"
      "      begin @(u.a & 1'b1) hits = hits + 10; end\n"
      "      begin #1 u.a = 1'b1; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// The referencing scope declares `a` of its own, so a walk that collected the
// leaf name alone finds a variable and arms a watcher on it -- the wrong one.
// Only the instance's `a` is driven, and the local one is not, so a process
// following the local name never resumes. This is what separates flattening the
// name from happening upon a variable of the same leaf name.
TEST(EventControlSim, CompoundEventFollowsTheHierarchicalNameNotTheLocalOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic a;\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "  logic a;\n"
      "  int hit;\n"
      "  initial begin\n"
      "    hit = 0;\n"
      "    a = 1'b0;\n"
      "    fork\n"
      "      begin @(u.a & 1'b1) hit = 1; end\n"
      "      begin #1 u.a = 1'b1; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2: an event control on a packed structure resumes on a write to one of
// its members, because a member write changes the value the event control
// names. The write has to be a member write: an assignment to the whole
// variable, and equally a bit-select or part-select of it, rebuilds the
// variable's value, so a watcher holding a stale reference to the old
// representation would still see the two apart. A packed-struct member write
// deposits into the words the variable already holds, so only a watcher that
// kept a value of its own can tell the before from the after.
TEST(EventControlSim, PackedStructMemberWriteFiresAnyChangeEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t s;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    s = 8'h00;\n"
      "    x = 8'd7;\n"
      "    #5 s.b = 4'h1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(s) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §9.4.2: a posedge event control on a packed structure resumes when a member
// write drives bit 0 of the structure from 0 to 1. A packed structure lays its
// last member out in the low bits (§7.2.1), so `b` covers bits [3:0] and
// `s.b = 4'h1` is the write that moves bit 0. As above, a whole-variable
// assignment or a select assignment replaces the variable's value and so could
// not fail this; the member write edits the value in place, and the edge is
// visible only to a watcher holding its own copy of the previous value.
TEST(EventControlSim, PackedStructMemberWriteFiresPosedge) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t s;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    s = 8'h00;\n"
      "    x = 8'd7;\n"
      "    #5 s.b = 4'h1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge s) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §9.4.2: successive event controls on a packed structure each resume on the
// next member write. The waiter here is offered three member writes: one that
// deposits the value the member already holds, which is no change and leaves
// the first event control still waiting, then two that do change it. So the
// first event control's watcher has to carry its baseline across a
// notification it did not resume on, and the second event control has to arm a
// baseline of its own afterwards. Every one of the three writes edits the
// structure's value in place, which is why a whole-variable or select
// assignment could not stand in for any of them.
TEST(EventControlSim, SuccessivePackedStructMemberWritesResumeTwoWaits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t s;\n"
      "  logic [7:0] first_hit, second_hit;\n"
      "  initial begin\n"
      "    s = 8'h00;\n"
      "    first_hit = 8'd1;\n"
      "    second_hit = 8'd2;\n"
      "    #5 s.b = 4'h0;\n"
      "    #5 s.b = 4'h1;\n"
      "    #5 s.a = 4'h2;\n"
      "  end\n"
      "  initial begin\n"
      "    @(s) first_hit = 8'd55;\n"
      "    @(s) second_hit = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("first_hit")->value.ToUint64(), 55u);
  EXPECT_EQ(f.ctx.FindVariable("second_hit")->value.ToUint64(), 66u);
}

}  // namespace
