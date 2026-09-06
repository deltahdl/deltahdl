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

}  // namespace
