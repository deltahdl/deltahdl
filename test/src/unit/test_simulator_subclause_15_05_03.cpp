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
  auto result = EvalEvTriggered(true);
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
