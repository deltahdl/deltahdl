#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_stmt_exec.h"
#include "parser/ast_expr.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"

namespace {

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

TEST(IpcSync, WaitBlocksUntilTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, TriggerBeforeWaitLeavesProcessBlocked) {
  LowerFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IpcSync, WaitWithBodyExecutesAfterTrigger) {
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
      "    @(ev) x = 8'd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, BareAtSyntaxBlocksUntilTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @ev;\n"
      "    result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #3 ->ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, RepeatedWaitCatchesSuccessiveTriggers) {
  LowerFixture f;
  auto* var = RunAndFindVar(
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
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(IpcSync, HierarchicalEventWaitBlocksUntilTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module child;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(c1.ev);\n"
      "    result = 32'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, BareAtSyntaxWithHierarchicalEventBlocksUntilTrigger) {
  LowerFixture f;
  auto* var = RunAndFindVar(
      "module child;\n"
      "  event ev;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @c1.ev;\n"
      "    result = 32'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(IpcSync, EventControlOperatorDispatchesEdgeAndNamedEvent) {
  LowerFixture f;
  auto [a, b] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  event ev;\n"
                                 "  logic clk;\n"
                                 "  logic [7:0] a, b;\n"
                                 "  initial begin\n"
                                 "    clk = 0;\n"
                                 "    #5 clk = 1;\n"
                                 "    #5 -> ev;\n"
                                 "    #1 $finish;\n"
                                 "  end\n"
                                 "  initial begin\n"
                                 "    @(posedge clk) a = 8'd11;\n"
                                 "    @(ev) b = 8'd22;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "a", "b");
  EXPECT_EQ(a, 11u);
  EXPECT_EQ(b, 22u);
}

// §15.5.2 with §6.21: an event declared as a local of an automatic task, or as
// an automatic local of a begin-end block, is a named event of its frame, so
// the wait on it in one fork branch is woken by the trigger in the other: 1
// and 2, read as 12. Taken for a value, each wait waited for a change the
// trigger never made, and neither time was written.
TEST(NamedEventSim, AutomaticLocalEventsWakeTheirWaiters) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int t1, t2, r;\n"
      "  task automatic loc();\n"
      "    event le;\n"
      "    fork\n"
      "      begin @le; t1 = $time; end\n"
      "      #1 -> le;\n"
      "    join\n"
      "  endtask\n"
      "  initial begin\n"
      "    loc();\n"
      "    begin\n"
      "      automatic event be;\n"
      "      fork\n"
      "        begin @be; t2 = $time; end\n"
      "        #1 -> be;\n"
      "      join\n"
      "    end\n"
      "    r = t1 * 10 + t2;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

// §15.5.2 with §9.3.2 and §24.3: an event declared in a program instance is
// woken by the trigger a sibling fork branch of the program makes, both
// branches naming the program's own e: 3. The branch triggered the top's e,
// which no one waited on, and the wait was never woken.
TEST(NamedEventSim, ProgramEventIsWokenByASiblingBranch) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  event e;\n"
                       "  initial fork\n"
                       "    begin @e; $display(\"woke at %0t\", $time); end\n"
                       "    #3 -> e;\n"
                       "  join\n"
                       "endprogram\n"
                       "module t;\n"
                       "  p pi();\n"
                       "endmodule\n",
                       f),
            "woke at 3\n");
}

// §15.5.2 with §7.10: an event pushed into a queue of events is the event
// itself, so the wait on q[0] is woken by the trigger of e at 2. Pushed as a
// value, the element named no event and the wait was never woken.
TEST(NamedEventSim, EventPushedIntoAQueueIsTheSameEvent) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event q[$];\n"
      "  event e;\n"
      "  int at;\n"
      "  initial begin\n"
      "    q.push_back(e);\n"
      "    fork\n"
      "      begin @q[0]; at = $time; end\n"
      "      #2 -> e;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f, "at");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
