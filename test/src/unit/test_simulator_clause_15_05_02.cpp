// §15.5.2: Waiting for an event

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace {

// =============================================================================
// 13. Event triggered state (section 15.5.2)
// =============================================================================
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

// =============================================================================
// 16. Event trigger in stmt_exec sets triggered state
// =============================================================================
TEST(IpcSync, EventTriggerSetsTriggeredState) {
  SyncFixture f;
  // Create named event variable.
  auto* ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  // Build event trigger statement: ->my_event
  auto* trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kEventTrigger;
  trigger_stmt->expr = f.arena.Create<Expr>();
  trigger_stmt->expr->kind = ExprKind::kIdentifier;
  trigger_stmt->expr->text = "my_event";

  // Execute trigger via a driver coroutine.
  auto driver = [](const Stmt* stmt, SimContext& ctx, Arena& arena,
                   DriverResult* out) -> SimCoroutine {
    out->value = co_await ExecStmt(stmt, ctx, arena);
  };
  DriverResult result;
  auto coro = driver(trigger_stmt, f.ctx, f.arena, &result);
  coro.Resume();

  EXPECT_TRUE(f.ctx.IsEventTriggered("my_event"));
}

// =============================================================================
// 25. Event triggered state is sticky within timeslot
// =============================================================================
TEST(IpcSync, EventTriggeredStickyWithinTimeslot) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  // Should still be triggered (same timeslot).
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  // Different event should not be triggered.
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

}  // namespace
