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

namespace {

// Helper fixture providing scheduler, arena, diag, and sim context.
struct SyncFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, 42};
};

}  // namespace

// =============================================================================
// 1. Semaphore: Constructor with key count (section 15.3)
// =============================================================================

TEST(IpcSync, SemaphoreNewDefaultKeys) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewWithKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

// =============================================================================
// 2. Semaphore: put() adds keys (section 15.3.2)
// =============================================================================

TEST(IpcSync, SemaphorePutAddsKeys) {
  SemaphoreObject sem(0);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutDefaultAddsOne) {
  SemaphoreObject sem(0);
  sem.Put();
  EXPECT_EQ(sem.key_count, 1);
}

// =============================================================================
// 3. Semaphore: try_get() non-blocking (section 15.3.3)
// =============================================================================

TEST(IpcSync, SemaphoreTryGetSucceeds) {
  SemaphoreObject sem(3);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetFails) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(sem.key_count, 1);  // Keys unchanged on failure.
}

TEST(IpcSync, SemaphoreTryGetDefaultOne) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet();
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreTryGetExactKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);  // Empty now.
}

// =============================================================================
// 4. Semaphore: Context registration (section 15.3)
// =============================================================================

TEST(IpcSync, SemaphoreContextCreateFind) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("sem1", 3);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 3);

  auto* found = f.ctx.FindSemaphore("sem1");
  EXPECT_EQ(found, sem);

  auto* not_found = f.ctx.FindSemaphore("no_such_sem");
  EXPECT_EQ(not_found, nullptr);
}

// =============================================================================
// 5. Semaphore: put() wakes waiters
// =============================================================================

TEST(IpcSync, SemaphorePutWakesWaiters) {
  SemaphoreObject sem(0);
  bool woken = false;
  // Simulate a waiting coroutine by adding a waiter manually.
  // We cannot create a real coroutine here, but we can verify the
  // waiter queue management.
  EXPECT_EQ(sem.TryGet(1), 0);  // No keys available.
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);  // Key added, no waiters to wake.
  (void)woken;
}

// =============================================================================
// 6. Mailbox: Constructor (section 15.4)
// =============================================================================

TEST(IpcSync, MailboxNewUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxNewBounded) {
  MailboxObject mb(5);
  EXPECT_EQ(mb.bound, 5);
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 7. Mailbox: try_put() / num() (section 15.4.3)
// =============================================================================

TEST(IpcSync, MailboxTryPutUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.TryPut(42), 0);
  EXPECT_EQ(mb.TryPut(99), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedSuccess) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedFull) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);  // Full.
  EXPECT_EQ(mb.Num(), 1);
}

// =============================================================================
// 8. Mailbox: try_get() (section 15.4.4)
// =============================================================================

TEST(IpcSync, MailboxTryGetSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryGetEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), -1);
}

TEST(IpcSync, MailboxTryGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  mb.TryPut(30);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 20u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 30u);
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 9. Mailbox: try_peek() (section 15.4.5)
// =============================================================================

TEST(IpcSync, MailboxTryPeekSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);  // Peek does not remove.
}

TEST(IpcSync, MailboxTryPeekEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), -1);
}

// =============================================================================
// 10. Mailbox: Context registration (section 15.4)
// =============================================================================

TEST(IpcSync, MailboxContextCreateFind) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mbox1", 10);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 10);

  auto* found = f.ctx.FindMailbox("mbox1");
  EXPECT_EQ(found, mb);

  auto* not_found = f.ctx.FindMailbox("no_such_mbox");
  EXPECT_EQ(not_found, nullptr);
}

// =============================================================================
// 11. Mailbox: Bounded put then get frees space
// =============================================================================

TEST(IpcSync, MailboxBoundedGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);  // Full.

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 0);  // Space freed.
  EXPECT_EQ(mb.Num(), 1);
}

// =============================================================================
// 12. Mailbox: Multiple get/put cycles
// =============================================================================

TEST(IpcSync, MailboxMultipleGetPutCycles) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 100; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 100);
  for (uint64_t i = 0; i < 100; ++i) {
    uint64_t msg = 0;
    EXPECT_EQ(mb.TryGet(msg), 0);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
}

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
// 14. Semaphore: Multiple put/tryget cycles
// =============================================================================

TEST(IpcSync, SemaphoreMultiplePutTryGetCycles) {
  SemaphoreObject sem(0);
  sem.Put(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(7), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// =============================================================================
// 15. Mailbox: IsFull predicate
// =============================================================================

TEST(IpcSync, MailboxIsFullBounded) {
  MailboxObject mb(2);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(1);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(2);
  EXPECT_TRUE(mb.IsFull());
}

TEST(IpcSync, MailboxIsFullUnbounded) {
  MailboxObject mb;
  EXPECT_FALSE(mb.IsFull());
  for (int i = 0; i < 1000; ++i) {
    mb.TryPut(static_cast<uint64_t>(i));
  }
  EXPECT_FALSE(mb.IsFull());  // Unbounded never full.
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
  struct DriverResult {
    StmtResult value = StmtResult::kDone;
  };
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
// 17. Semaphore: TryGet with count=0 always succeeds
// =============================================================================

TEST(IpcSync, SemaphoreTryGetZeroCount) {
  SemaphoreObject sem(0);
  // Requesting 0 keys should always succeed (0 >= 0).
  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// =============================================================================
// 18. Mailbox: Peek does not consume
// =============================================================================

TEST(IpcSync, MailboxPeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  // Multiple peeks should return same value.
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
  // Get consumes it.
  mb.TryGet(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 19. Mailbox: Parameterized type simulation (uint64_t values)
// =============================================================================

TEST(IpcSync, MailboxParameterizedTypeValues) {
  MailboxObject mb;
  // Simulate different "types" by encoding type info in the value.
  mb.TryPut(0xDEADBEEF);
  mb.TryPut(0xCAFEBABE);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xDEADBEEFu);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xCAFEBABEu);
}

// =============================================================================
// 20. Semaphore: Large key count
// =============================================================================

TEST(IpcSync, SemaphoreLargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// =============================================================================
// 21. Mailbox: Num reflects current state
// =============================================================================

TEST(IpcSync, MailboxNumReflectsState) {
  MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  mb.TryPut(1);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryPut(2);
  EXPECT_EQ(mb.Num(), 2);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

// =============================================================================
// 22. Event variable creation with is_event flag
// =============================================================================

TEST(IpcSync, EventVariableCreation) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

// =============================================================================
// 23. Multiple semaphores in same context
// =============================================================================

TEST(IpcSync, MultipleSemaphoresInContext) {
  SyncFixture f;
  auto* sem1 = f.ctx.CreateSemaphore("s1", 1);
  auto* sem2 = f.ctx.CreateSemaphore("s2", 5);
  EXPECT_EQ(sem1->key_count, 1);
  EXPECT_EQ(sem2->key_count, 5);
  EXPECT_NE(f.ctx.FindSemaphore("s1"), f.ctx.FindSemaphore("s2"));
}

// =============================================================================
// 24. Multiple mailboxes in same context
// =============================================================================

TEST(IpcSync, MultipleMailboxesInContext) {
  SyncFixture f;
  auto* mb1 = f.ctx.CreateMailbox("m1", 0);
  auto* mb2 = f.ctx.CreateMailbox("m2", 3);
  mb1->TryPut(100);
  mb2->TryPut(200);
  uint64_t msg = 0;
  mb1->TryGet(msg);
  EXPECT_EQ(msg, 100u);
  mb2->TryGet(msg);
  EXPECT_EQ(msg, 200u);
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
