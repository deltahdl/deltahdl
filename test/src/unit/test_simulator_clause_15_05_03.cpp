#include <gtest/gtest.h>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/stmt_exec.h"

namespace {

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

TEST(IpcSync, TriggeredMethodReturnsOneWhenTriggered) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);
  f.ctx.SetEventTriggered("ev");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(IpcSync, TriggeredMethodYieldsSingleBit) {
  // §15.5.3: triggered is prototyped as a bit-valued method, so the evaluated
  // result is a single-bit quantity regardless of the event's triggered state.
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);
  f.ctx.SetEventTriggered("ev");

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(IpcSync, TriggeredMethodReturnsZeroByDefault) {
  SimFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* access = f.arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = MakeId(f.arena, "ev");
  access->rhs = MakeId(f.arena, "triggered");

  auto result = EvalExpr(access, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(IpcSync, WaitTriggeredProceedsWhenAlreadyTriggered) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(IpcSync, WaitTriggeredUnblocksInFork) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitTriggeredUnblocksWhenWaitPrecedesSameTimeTrigger) {
  // §15.5.3: a process waiting on the triggered state unblocks regardless of
  // execution order at the same simulation time. Here the waiting branch runs
  // and blocks first, then the trigger fires later in the same step.
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(IpcSync, WaitTriggeredUnblocksWhenTriggerAfterWait) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
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

}  // namespace
