#include <gtest/gtest.h>

#include <string_view>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §15.5.1 Triggering events — -> (blocking), ->> (nonblocking)
// ---------------------------------------------------------------------------

TEST(NamedEventSync, BlockingTriggerAndWait) {
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
      "    #5 ->ev;\n"
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

TEST(NamedEventSync, BareWaitSyntax) {
  LowerFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(NamedEventSync, TriggerAndWaitWithBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #5 -> ev;\n"
      "  end\n"
      "  initial begin\n"
      "    @(ev) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(NamedEventSync, TriggerSetsTriggeredState) {
  SyncFixture f;

  auto* ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kEventTrigger;
  trigger_stmt->expr = MakeId(f.arena, "my_event");

  DriverResult result;
  auto coro = DriverCoroutine(trigger_stmt, f.ctx, f.arena, &result);
  coro.Resume();

  EXPECT_TRUE(f.ctx.IsEventTriggered("my_event"));
}

TEST(NamedEventSync, NonblockingTriggerReturnsKDone) {
  // §15.5.1: ->> schedules trigger in NBA region. Stmt should return kDone.
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kNbEventTrigger;
  stmt->expr = MakeId(f.arena, "ev");

  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// ---------------------------------------------------------------------------
// §15.5.2 Waiting for events — @(event)
// ---------------------------------------------------------------------------

TEST(NamedEventSync, EventVariableCreation) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

// ---------------------------------------------------------------------------
// §15.5.3 .triggered method
// ---------------------------------------------------------------------------

TEST(NamedEventSync, TriggeredDefaultIsFalse) {
  SyncFixture f;
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev1"));
}

TEST(NamedEventSync, TriggeredSetAndCheck) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
}

TEST(NamedEventSync, TriggeredDifferentNames) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

TEST(NamedEventSync, TriggeredStickyWithinTimeslot) {
  // §15.5.3: .triggered remains true for the entire timestep.
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");

  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));

  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

// ---------------------------------------------------------------------------
// §15.5.4 wait_order()
// ---------------------------------------------------------------------------

TEST(NamedEventSync, WaitOrderImmediateReturnsKDone) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev1"));
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev2"));

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// ---------------------------------------------------------------------------
// §15.5.5 Event variables — creation, merging, reclaiming
// ---------------------------------------------------------------------------

TEST(NamedEventSync, EventVariableIsEventFlag) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  EXPECT_FALSE(ev->is_event);
  ev->is_event = true;
  EXPECT_TRUE(ev->is_event);
}

TEST(NamedEventSync, MultipleEventVariables) {
  SyncFixture f;
  auto* ev1 = f.ctx.CreateVariable("ev1", 1);
  ev1->is_event = true;
  auto* ev2 = f.ctx.CreateVariable("ev2", 1);
  ev2->is_event = true;

  EXPECT_NE(f.ctx.FindVariable("ev1"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("ev2"), nullptr);
  EXPECT_TRUE(f.ctx.FindVariable("ev1")->is_event);
  EXPECT_TRUE(f.ctx.FindVariable("ev2")->is_event);
}

TEST(NamedEventSync, TriggerWakesWatchers) {
  // §15.5.1: -> wakes all processes blocked on @(event).
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  bool watcher_called = false;
  ev->AddWatcher([&watcher_called]() {
    watcher_called = true;
    return true;
  });

  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kEventTrigger;
  trigger_stmt->expr = MakeId(f.arena, "ev");

  DriverResult result;
  auto coro = DriverCoroutine(trigger_stmt, f.ctx, f.arena, &result);
  coro.Resume();
  // The watcher callback is scheduled as an event; run the scheduler.
  f.scheduler.Run();

  EXPECT_TRUE(watcher_called);
}

}  // namespace
