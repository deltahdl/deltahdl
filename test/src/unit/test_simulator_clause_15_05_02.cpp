// §15.5.2: Waiting for an event

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/sync_objects.h"
#include "simulation/variable.h"

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
struct SyncFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, 42};
};

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
  auto *ev = f.ctx.CreateVariable("my_event", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  // Build event trigger statement: ->my_event
  auto *trigger_stmt = f.arena.Create<Stmt>();
  trigger_stmt->kind = StmtKind::kEventTrigger;
  trigger_stmt->expr = f.arena.Create<Expr>();
  trigger_stmt->expr->kind = ExprKind::kIdentifier;
  trigger_stmt->expr->text = "my_event";

  // Execute trigger via a driver coroutine.
  struct DriverResult {
    StmtResult value = StmtResult::kDone;
  };
  auto driver = [](const Stmt *stmt, SimContext &ctx, Arena &arena,
                   DriverResult *out) -> SimCoroutine {
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
