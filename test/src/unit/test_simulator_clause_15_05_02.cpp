#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"

namespace {

// --- §15.5.2 event triggered state (moved from test_simulator_clause_15_05_03) ---

TEST(IpcSync, EventTriggeredDefault) {
  SyncFixture f;
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev1"));
}

TEST(IpcSync, EventTriggeredSetAndCheck) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
}

TEST(IpcSync, EventTriggeredDifferentNames) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

TEST(IpcSync, EventTriggerSetsTriggeredState) {
  SyncFixture f;

  auto* ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kEventTrigger;
  trigger_stmt->expr = f.arena.Create<Expr>();
  trigger_stmt->expr->kind = ExprKind::kIdentifier;
  trigger_stmt->expr->text = "my_event";

  auto driver = [](const Stmt* stmt, SimContext& ctx, Arena& arena,
                   DriverResult* out) -> SimCoroutine {
    out->value = co_await ExecStmt(stmt, ctx, arena);
  };
  DriverResult result;
  auto coro = driver(trigger_stmt, f.ctx, f.arena, &result);
  coro.Resume();

  EXPECT_TRUE(f.ctx.IsEventTriggered("my_event"));
}

TEST(IpcSync, EventTriggeredStickyWithinTimeslot) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");

  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));

  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

// --- §15.5.2 waiting-for-event simulation tests ---

// §15.5.2: @ blocks until trigger fires (wait-then-trigger ordering).
TEST(IpcSync, WaitBlocksUntilTrigger) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 42;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §15.5.2: If trigger fires before @ executes, waiter remains blocked.
TEST(IpcSync, TriggerBeforeWaitLeavesProcessBlocked) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "    #10 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    @(ev);\n"
      "    result = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §15.5.2: @ with body statement executes body after trigger.
TEST(IpcSync, WaitWithBodyExecutesAfterTrigger) {
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
      "    @(ev) x = 8'd99;\n"
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

// §15.5.2: Repeated @ in a loop catches successive triggers.
TEST(IpcSync, RepeatedWaitCatchesSuccessiveTriggers) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    @(ev) count = count + 1;\n"
      "    @(ev) count = count + 1;\n"
      "    @(ev) count = count + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> ev;\n"
      "    #1 -> ev;\n"
      "    #1 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
