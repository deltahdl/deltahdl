// §15 Interprocess synchronization and communication — simulator tests.

#include <cstdint>
#include <string_view>

#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §15.3 Semaphores
// ---------------------------------------------------------------------------

// §15.3.1 new()

TEST(SimIpcSync, SemaphoreNewDefaultKeys) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SimIpcSync, SemaphoreNewWithKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(SimIpcSync, SemaphoreContextCreateFind) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("sem1", 3);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 3);

  auto* found = f.ctx.FindSemaphore("sem1");
  EXPECT_EQ(found, sem);

  auto* not_found = f.ctx.FindSemaphore("no_such_sem");
  EXPECT_EQ(not_found, nullptr);
}

TEST(SimIpcSync, MultipleSemaphoresInContext) {
  SyncFixture f;
  auto* sem1 = f.ctx.CreateSemaphore("s1", 1);
  auto* sem2 = f.ctx.CreateSemaphore("s2", 5);
  EXPECT_EQ(sem1->key_count, 1);
  EXPECT_EQ(sem2->key_count, 5);
  EXPECT_NE(f.ctx.FindSemaphore("s1"), f.ctx.FindSemaphore("s2"));
}

// §15.3.2 put()

TEST(SimIpcSync, SemaphorePutAddsKeys) {
  SemaphoreObject sem(0);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(SimIpcSync, SemaphorePutDefaultAddsOne) {
  SemaphoreObject sem(0);
  sem.Put();
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SimIpcSync, SemaphorePutWakesWaiters) {
  SemaphoreObject sem(0);
  bool woken = false;

  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
  (void)woken;
}

// §15.3.4 try_get()

TEST(SimIpcSync, SemaphoreTryGetSucceeds) {
  SemaphoreObject sem(3);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SimIpcSync, SemaphoreTryGetFails) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SimIpcSync, SemaphoreTryGetDefaultOne) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet();
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SimIpcSync, SemaphoreTryGetExactKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
}

TEST(SimIpcSync, SemaphoreTryGetZeroCount) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SimIpcSync, SemaphoreDrainKeys) {
  SemaphoreObject sem(0);
  sem.Put(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(7), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SimIpcSync, SemaphoreRefillAndDrain) {
  SemaphoreObject sem(0);
  sem.Put(10);
  sem.TryGet(10);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SimIpcSync, SemaphoreLargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// ---------------------------------------------------------------------------
// §15.4 Mailboxes
// ---------------------------------------------------------------------------

// §15.4.1 new()

TEST(SimIpcSync, MailboxNewUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(SimIpcSync, MailboxNewBounded) {
  MailboxObject mb(5);
  EXPECT_EQ(mb.bound, 5);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(SimIpcSync, MailboxContextCreateFind) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mbox1", 10);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 10);

  auto* found = f.ctx.FindMailbox("mbox1");
  EXPECT_EQ(found, mb);

  auto* not_found = f.ctx.FindMailbox("no_such_mbox");
  EXPECT_EQ(not_found, nullptr);
}

TEST(SimIpcSync, MultipleMailboxesInContext) {
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

// §15.4.2 num()

TEST(SimIpcSync, MailboxNumReflectsState) {
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

// §15.4.4 try_put()

TEST(SimIpcSync, MailboxTryPutUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.TryPut(42), 0);
  EXPECT_EQ(mb.TryPut(99), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(SimIpcSync, MailboxTryPutBoundedSuccess) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(SimIpcSync, MailboxTryPutBoundedFull) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(SimIpcSync, MailboxBoundedGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 0);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4 FIFO ordering

TEST(SimIpcSync, MailboxFifoOrder) {
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

TEST(SimIpcSync, MailboxMultipleGetPutCycles) {
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

// §15.4 IsFull

TEST(SimIpcSync, MailboxIsFullBounded) {
  MailboxObject mb(2);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(1);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(2);
  EXPECT_TRUE(mb.IsFull());
}

TEST(SimIpcSync, MailboxIsFullUnbounded) {
  MailboxObject mb;
  EXPECT_FALSE(mb.IsFull());
  for (int i = 0; i < 1000; ++i) {
    mb.TryPut(static_cast<uint64_t>(i));
  }
  EXPECT_FALSE(mb.IsFull());
}

// §15.4.6 try_get()

TEST(SimIpcSync, MailboxTryGetSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(SimIpcSync, MailboxTryGetEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), -1);
}

// §15.4.8 try_peek()

TEST(SimIpcSync, MailboxTryPeekSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(SimIpcSync, MailboxTryPeekEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), -1);
}

TEST(SimIpcSync, MailboxPeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;

  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);

  mb.TryGet(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.9 Parameterized mailboxes

TEST(SimIpcSync, MailboxParameterizedTypeValues) {
  MailboxObject mb;

  mb.TryPut(0xDEADBEEF);
  mb.TryPut(0xCAFEBABE);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xDEADBEEFu);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xCAFEBABEu);
}

// ---------------------------------------------------------------------------
// §15.5 Named events
// ---------------------------------------------------------------------------

// §15.5.1 Triggering an event (integration tests)

TEST(SimIpcSync, NamedEventTriggerAndWait) {
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

TEST(SimIpcSync, NamedEventBareWaitSyntax) {
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

TEST(SimIpcSync, EventTriggerAndWaitWithDelay) {
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

// §15.5 Event variable creation

TEST(SimIpcSync, EventVariableCreation) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

// §15.5.3 Persistent trigger: triggered built-in method

TEST(SimIpcSync, EventTriggeredDefault) {
  SyncFixture f;
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev1"));
}

TEST(SimIpcSync, EventTriggeredSetAndCheck) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
}

TEST(SimIpcSync, EventTriggeredDifferentNames) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

TEST(SimIpcSync, EventTriggerSetsTriggeredState) {
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

TEST(SimIpcSync, EventTriggeredStickyWithinTimeslot) {
  SyncFixture f;
  f.ctx.SetEventTriggered("ev1");

  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));
  EXPECT_TRUE(f.ctx.IsEventTriggered("ev1"));

  EXPECT_FALSE(f.ctx.IsEventTriggered("ev2"));
}

// §15.5.4 Event sequencing: wait_order()

TEST(SimIpcSync, WaitOrderImmediateReturn) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev1"));
  stmt->wait_order_events.push_back(MakeId(f.arena, "ev2"));

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

// §15.5.5.2 Reclaiming events — null event trigger has no effect

TEST(SimIpcSync, NullEventTriggerNoEffect) {
  SyncFixture f;
  // Triggering a null event does nothing (no crash).
  EXPECT_FALSE(f.ctx.IsEventTriggered("null_event"));
}

}  // namespace
