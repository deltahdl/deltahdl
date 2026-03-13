#include <gtest/gtest.h>

#include <coroutine>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

// ---------------------------------------------------------------------------
// §15.4.1 new() — Mailbox construction
// ---------------------------------------------------------------------------

TEST(MailboxSync, NewDefaultIsUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSync, NewWithBound) {
  MailboxObject mb(5);
  EXPECT_EQ(mb.bound, 5);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSync, NewNegativeBoundIsIllegal) {
  // §15.4.1: Negative bounds are illegal.
  MailboxObject mb(-1);
  EXPECT_LT(mb.bound, 0);
}

// ---------------------------------------------------------------------------
// §15.4.2 num() — Message count
// ---------------------------------------------------------------------------

TEST(MailboxSync, NumReturnsMessageCount) {
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

// ---------------------------------------------------------------------------
// §15.4.3 put() — Blocking message send (FIFO)
// ---------------------------------------------------------------------------

TEST(MailboxSync, PutStoresInFifoOrder) {
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

TEST(MailboxSync, PutBoundedAddsPutWaiterWhenFull) {
  // §15.4.3: On a bounded queue, put() suspends if full.
  MailboxObject mb(1);
  mb.TryPut(10);
  EXPECT_TRUE(mb.IsFull());

  auto noop = std::noop_coroutine();
  mb.AddPutWaiter(noop);
  EXPECT_EQ(mb.put_waiters.size(), 1u);
}

TEST(MailboxSync, GetWakesPutWaiter) {
  // §15.4.3: After get() frees space, a suspended put() waiter is woken.
  MailboxObject mb(1);
  mb.TryPut(10);

  auto noop = std::noop_coroutine();
  mb.AddPutWaiter(noop);
  EXPECT_EQ(mb.put_waiters.size(), 1u);

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_TRUE(mb.put_waiters.empty());
}

// ---------------------------------------------------------------------------
// §15.4.4 try_put() — Non-blocking message send
// ---------------------------------------------------------------------------

TEST(MailboxSync, TryPutUnboundedReturnsPositive) {
  // §15.4.4: Unbounded mailboxes are never full; returns positive.
  MailboxObject mb;
  EXPECT_GT(mb.TryPut(42), 0);
  EXPECT_GT(mb.TryPut(99), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(MailboxSync, TryPutBoundedSucceeds) {
  MailboxObject mb(2);
  EXPECT_GT(mb.TryPut(10), 0);
  EXPECT_GT(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(MailboxSync, TryPutBoundedFullReturnsZero) {
  // §15.4.4: If the mailbox is full, returns 0.
  MailboxObject mb(1);
  EXPECT_GT(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(MailboxSync, BoundedGetFreesSpaceForTryPut) {
  MailboxObject mb(1);
  EXPECT_GT(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), 0);

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_GT(mb.TryPut(30), 0);
  EXPECT_EQ(mb.Num(), 1);
}

// ---------------------------------------------------------------------------
// §15.4.5 get() — Blocking message retrieve
// ---------------------------------------------------------------------------

TEST(MailboxSync, GetBlocksWhenEmpty) {
  // §15.4.5: If empty, get() blocks until a message arrives.
  MailboxObject mb;
  EXPECT_TRUE(mb.IsEmpty());

  auto noop = std::noop_coroutine();
  mb.AddGetWaiter(noop);
  EXPECT_EQ(mb.get_waiters.size(), 1u);
}

TEST(MailboxSync, PutWakesGetWaiter) {
  // §15.4.5: A put() wakes a blocked get() waiter.
  MailboxObject mb;
  auto noop = std::noop_coroutine();
  mb.AddGetWaiter(noop);
  EXPECT_EQ(mb.get_waiters.size(), 1u);

  mb.TryPut(42);
  EXPECT_TRUE(mb.get_waiters.empty());
}

TEST(MailboxSync, GetWaitingQueueIsFifo) {
  // §15.4.5: Waiting queue preserves arrival order.
  MailboxObject mb;
  auto noop = std::noop_coroutine();
  mb.AddGetWaiter(noop);
  mb.AddGetWaiter(noop);
  EXPECT_EQ(mb.get_waiters.size(), 2u);

  // Only one get waiter wakes per message.
  mb.TryPut(1);
  EXPECT_EQ(mb.get_waiters.size(), 1u);
  mb.TryPut(2);
  EXPECT_TRUE(mb.get_waiters.empty());
}

// ---------------------------------------------------------------------------
// §15.4.6 try_get() — Non-blocking message retrieve
// ---------------------------------------------------------------------------

TEST(MailboxSync, TryGetSucceedsWithPositive) {
  // §15.4.6: Returns positive when a message is available.
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_GT(mb.TryGet(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSync, TryGetEmptyReturnsZero) {
  // §15.4.6: Returns 0 when empty.
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 0);
}

TEST(MailboxSync, TryGetRemovesMessage) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 20u);
  EXPECT_EQ(mb.Num(), 0);
}

// ---------------------------------------------------------------------------
// §15.4.7 peek() — Blocking non-consuming read
// ---------------------------------------------------------------------------

TEST(MailboxSync, PeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;

  EXPECT_GT(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_GT(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);

  mb.TryGet(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSync, PeekBlocksWhenEmpty) {
  // §15.4.7: If empty, peek() blocks.
  MailboxObject mb;
  auto noop = std::noop_coroutine();
  mb.AddPeekWaiter(noop);
  EXPECT_EQ(mb.peek_waiters.size(), 1u);
}

TEST(MailboxSync, PutWakesAllPeekWaiters) {
  // §15.4.7: A put() wakes all blocked peek() waiters.
  MailboxObject mb;
  auto noop = std::noop_coroutine();
  mb.AddPeekWaiter(noop);
  mb.AddPeekWaiter(noop);
  EXPECT_EQ(mb.peek_waiters.size(), 2u);

  mb.TryPut(1);
  EXPECT_TRUE(mb.peek_waiters.empty());
}

// ---------------------------------------------------------------------------
// §15.4.8 try_peek() — Non-blocking non-consuming read
// ---------------------------------------------------------------------------

TEST(MailboxSync, TryPeekSucceedsWithPositive) {
  // §15.4.8: Returns positive when a message is available.
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_GT(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(MailboxSync, TryPeekEmptyReturnsZero) {
  // §15.4.8: Returns 0 when empty.
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 0);
}

// ---------------------------------------------------------------------------
// §15.4.9 Parameterized mailboxes
// ---------------------------------------------------------------------------

TEST(MailboxSync, ParameterizedTypeValues) {
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
// Context integration
// ---------------------------------------------------------------------------

TEST(MailboxSync, ContextCreateAndFind) {
  SyncFixture f;
  auto* mb = f.ctx.CreateMailbox("mbox1", 10);
  ASSERT_NE(mb, nullptr);
  EXPECT_EQ(mb->bound, 10);

  auto* found = f.ctx.FindMailbox("mbox1");
  EXPECT_EQ(found, mb);
}

TEST(MailboxSync, ContextFindReturnsNullForUnknown) {
  SyncFixture f;
  EXPECT_EQ(f.ctx.FindMailbox("no_such_mbox"), nullptr);
}

TEST(MailboxSync, MultipleMailboxesInContext) {
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

TEST(MailboxSync, MultiplePutGetCycles) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 100; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 100);
  for (uint64_t i = 0; i < 100; ++i) {
    uint64_t msg = 0;
    EXPECT_GT(mb.TryGet(msg), 0);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSync, IsFullBounded) {
  MailboxObject mb(2);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(1);
  EXPECT_FALSE(mb.IsFull());
  mb.TryPut(2);
  EXPECT_TRUE(mb.IsFull());
}

TEST(MailboxSync, UnboundedNeverFull) {
  MailboxObject mb;
  for (int i = 0; i < 1000; ++i) {
    mb.TryPut(static_cast<uint64_t>(i));
  }
  EXPECT_FALSE(mb.IsFull());
}

}  // namespace
