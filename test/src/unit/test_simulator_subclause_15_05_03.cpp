#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"

namespace {

// Evaluates the `triggered` method of a named event under a fresh SimFixture.
// The event `ev` is created and optionally marked as triggered, then the
// member-access expression `ev.triggered` is evaluated and its result returned.
static Logic4Vec EvalEvTriggered(bool set_triggered) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);
  if (set_triggered) f.ctx.SetEventTriggered("ev");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  return EvalExpr(access, f.ctx, f.arena);
}

TEST(IpcSync, NonblockingTriggerSetsTriggeredState) {
  SyncFixture f;

  auto* ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kNbEventTrigger;
  trigger_stmt->expr = f.arena.Create<Expr>();
  trigger_stmt->expr->kind = ExprKind::kIdentifier;
  trigger_stmt->expr->text = "my_event";

  auto result = RunStmt(trigger_stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);

  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.IsEventTriggered("my_event"));
}

TEST(IpcSync, TriggeredMethodYieldsSingleBit) {
  // §15.5.3: triggered is prototyped as a bit-valued method, so the evaluated
  // result is a single-bit quantity regardless of the event's triggered state.
  auto result = EvalEvTriggered(/*set_triggered=*/true);
  EXPECT_EQ(result.width, 1u);
}

TEST(IpcSync, WaitTriggeredProceedsWhenAlreadyTriggered) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    wait(ev.triggered);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(IpcSync, WaitTriggeredUnblocksInFork) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event blast;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      -> blast;\n"
      "      begin wait(blast.triggered); result = 42; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitTriggeredUnblocksWhenWaitPrecedesSameTimeTrigger) {
  // §15.5.3: a process waiting on the triggered state unblocks regardless of
  // execution order at the same simulation time. Here the waiting branch runs
  // and blocks first, then the trigger fires later in the same step.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin wait(ev.triggered); result = 33; end\n"
      "      -> ev;\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(IpcSync, WaitTriggeredUnblocksWhenTriggerAfterWait) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait(ev.triggered);\n"
      "    result = 77;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(IpcSync, NullEventTriggeredReturnsFalse) {
  SimFixture f;
  f.ctx.NullifyEventVariable("ev");
  // §15.5.3: a null named event's triggered method is false even if a trigger
  // tick happens to match the current time step, so record one to prove the
  // null case is handled distinctly from the merely-never-triggered case.
  f.ctx.SetEventTriggered("ev");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(IpcSync, WaitTriggeredWithBodyStatement) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  initial\n"
      "    wait(ev.triggered) x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, TriggeredStateClearsAfterTimeAdvances) {
  // §15.5.3: the triggered state holds for the whole time step in which the
  // event fired and then clears once simulation time advances. Reading it in
  // the same step yields 1; reading it after a delay yields 0.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] same_step;\n"
      "  logic [7:0] next_step;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    if (ev.triggered) same_step = 8'd1; else same_step = 8'd0;\n"
      "    #1;\n"
      "    if (ev.triggered) next_step = 8'd1; else next_step = 8'd0;\n"
      "  end\n"
      "  initial #2 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* same = f.ctx.FindVariable("same_step");
  auto* next = f.ctx.FindVariable("next_step");
  ASSERT_NE(same, nullptr);
  ASSERT_NE(next, nullptr);
  EXPECT_EQ(same->value.ToUint64(), 1u);
  EXPECT_EQ(next->value.ToUint64(), 0u);
}

TEST(IpcSync, WaitOnNullEventTriggeredNeverUnblocks) {
  // §15.5.3: the triggered method of a null named event is always false, so a
  // process waiting on it has no condition that can ever hold and must remain
  // blocked. The value set before the wait therefore survives to end of sim.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd5;\n"
      "    wait(ev.triggered);\n"
      "    result = 8'd9;\n"
      "  end\n"
      "  initial #3 $finish;\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(IpcSync, TriggeredStatePersistsAcrossSuccessiveWaitsInSameStep) {
  // §15.5.3: the triggered state holds for the whole time step in which the
  // event fired, so more than one wait evaluated within that same step observes
  // it and unblocks. Both waits clear at time 0 with no time advance between.
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] first;\n"
      "  logic [7:0] second;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    wait(ev.triggered);\n"
      "    first = 8'd1;\n"
      "    wait(ev.triggered);\n"
      "    second = 8'd1;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* first = f.ctx.FindVariable("first");
  auto* second = f.ctx.FindVariable("second");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 1u);
  EXPECT_EQ(second->value.ToUint64(), 1u);
}

TEST(IpcSync, TriggeredCallFormEvaluatesTrueWhenTriggered) {
  // §15.5.3: the method is prototyped `function bit triggered()`, so invoking
  // it with explicit empty parentheses is equivalent to the bare-member form.
  // After the event fires in this step, ev.triggered() reads back true.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] hit;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    if (ev.triggered()) hit = 8'd1; else hit = 8'd0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, TriggeredCallFormEvaluatesFalseWhenNotTriggered) {
  // §15.5.3: with no trigger in the current step, the call form yields 1'b0
  // just as the bare-member form does, so the else branch runs.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] hit;\n"
      "  initial begin\n"
      "    if (ev.triggered()) hit = 8'd1; else hit = 8'd0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, TriggeredCallFormOnNullEventReturnsFalse) {
  // §15.5.3: the triggered method of a null named event returns false. This
  // must hold for the parenthesized call form as well as the bare-member form,
  // so a procedural read of ev.triggered() on a null event assigns 0.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev = null;\n"
      "  logic [7:0] hit;\n"
      "  initial begin\n"
      "    hit = ev.triggered();\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, TriggeredStateVisibleThroughEventAlias) {
  // §15.5.3: the triggered state is a property of the underlying named-event
  // synchronization object, not of the name used to reach it. The example
  // introduces an alias (event done_too = done) to make this point. Triggering
  // `done` and reading `done_too.triggered` in the same step observes the state
  // through the alias, so the if-branch runs.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "  logic [7:0] hit;\n"
      "  initial begin\n"
      "    -> done;\n"
      "    if (done_too.triggered) hit = 8'd1; else hit = 8'd0;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, NonblockingTriggerEndToEndSetsTriggeredState) {
  // §15.5.3: the persistent triggered state records that the event fired in the
  // current step regardless of which trigger operator produced it. Here the
  // event is fired with the §15.5.1 nonblocking trigger ->>, whose effect lands
  // in the nonblocking region of the same step; a sibling wait on the triggered
  // state then unblocks and runs the following assignment.
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] hit;\n"
      "  initial begin\n"
      "    ->> ev;\n"
      "    wait(ev.triggered);\n"
      "    hit = 8'd1;\n"
      "  end\n"
      "  initial #2 $finish;\n"
      "endmodule\n",
      f, "hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §15.5.3 with §6.17: `triggered` on a class's event property is 1 in the time
// step of its trigger, read in a method of the class right after `-> e` and
// through the handle by a wait on `s.e.triggered` in a sibling branch, which
// the trigger at 1 satisfies: 1 and 1, read as 11. Found by no name, the
// method read 0 and the wait was never satisfied.
TEST(NamedEventSim, TriggeredOnAClassEventProperty) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class Sync;\n"
      "    event e;\n"
      "    function bit fire(); -> e; return e.triggered; endfunction\n"
      "  endclass\n"
      "  Sync s;\n"
      "  int tr, at, r;\n"
      "  initial begin\n"
      "    s = new;\n"
      "    tr = s.fire();\n"
      "    #1;\n"
      "    fork\n"
      "      -> s.e;\n"
      "      begin wait (s.e.triggered); at = $time; end\n"
      "    join\n"
      "    r = tr * 10 + at;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// §15.5.3 with §9.4.2 and §13.5.5: `triggered` is a method of no arguments,
// written with or without `()`, and an event expression holding it is
// reevaluated when its event prefix is triggered. Both spellings wake at the
// trigger at 3, read as 33. The spelling without `()` named no variable and
// armed on nothing, so that process waited for the rest of the run.
TEST(NamedEventSim, EventControlOnTriggeredWakesWithOrWithoutParentheses) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int a, c, r;\n"
      "  initial begin @(e.triggered); a = $time; end\n"
      "  initial begin @(e.triggered()); c = $time; end\n"
      "  initial #3 -> e;\n"
      "  initial #10 r = a * 10 + c;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §15.5.3 with §9.4.2: the rise of `triggered` at the trigger is a posedge of
// the expression, in either spelling: 3 and 3, read as 33.
TEST(NamedEventSim, PosedgeOfTriggeredWakesAtTheTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int a, c, r;\n"
      "  initial begin @(posedge e.triggered); a = $time; end\n"
      "  initial begin @(posedge e.triggered()); c = $time; end\n"
      "  initial #3 -> e;\n"
      "  initial #10 r = a * 10 + c;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §15.5.3 with §9.4.2.1: `triggered` as one operand of an `or` wakes the
// process when its event is triggered, with the other operand untouched.
TEST(NamedEventSim, TriggeredAsOneOperandOfAnOrWakesAtTheTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic x = 0;\n"
      "  int a;\n"
      "  initial begin @(e.triggered or x); a = $time; end\n"
      "  initial #4 -> e;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §15.5.3 with §23.6: the event prefix may be a hierarchical name, here a
// child instance's event triggered by the child at 5.
TEST(NamedEventSim, TriggeredOfAHierarchicalEventWakesAtTheTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module c;\n"
      "  event e;\n"
      "  initial #5 -> e;\n"
      "endmodule\n"
      "module t;\n"
      "  c u();\n"
      "  int a;\n"
      "  initial begin @(u.e.triggered); a = $time; end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §15.5.3 with §6.17: the event prefix may be a class's event property,
// reached through a handle and triggered through it at 2.
TEST(NamedEventSim, TriggeredOfAClassEventPropertyWakesAtTheTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class Sync; event e; endclass\n"
      "  Sync s = new;\n"
      "  int a;\n"
      "  initial begin @(s.e.triggered); a = $time; end\n"
      "  initial #2 -> s.e;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §15.5.3 with §15.5.1: a nonblocking trigger sets the triggered state in the
// NBA region, so the woken process reads the value the triggering process
// went on to write after `->> e` in the Active region: 2, at time 3, read as
// 32.
TEST(NamedEventSim, NonblockingTriggerWakesTriggeredAfterTheActiveRegion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  int v, r;\n"
      "  initial begin @(e.triggered); r = $time * 10 + v; end\n"
      "  initial begin #3 v = 1; ->> e; v = 2; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

// §15.5.3: the return of `triggered` to 0 as time advances changes no operand
// of the expression, so a negedge of it never occurs; nor does an event
// control armed after the trigger in the same time step see a change, and a
// null event is never triggered at all. None of the three processes runs.
TEST(NamedEventSim, TriggeredWakesNoProcessWithoutAFreshTrigger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e, n = null;\n"
      "  int hits;\n"
      "  initial begin @(negedge e.triggered); hits += 1; end\n"
      "  initial begin #3 -> e; @(e.triggered); hits += 10; end\n"
      "  initial begin @(n.triggered); hits += 100; end\n"
      "  initial #3 -> n;\n"
      "  initial #20 $finish;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
