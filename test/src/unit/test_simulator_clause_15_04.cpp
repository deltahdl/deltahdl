#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace {

// Minimal coroutine modelling a process that performs a mailbox put(). It
// starts suspended; the first resume() runs it to the co_await, where
// MailboxPutAwaiter either stores the message right away (room available) or
// parks the handle on the mailbox's put-waiter queue. A later get() that frees
// a slot resumes it via WakePutWaiters(), and the body records that it ran.
struct BlockingPutter {
  struct promise_type {
    BlockingPutter get_return_object() {
      return BlockingPutter{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
  std::coroutine_handle<promise_type> h;
};

inline BlockingPutter SpawnPutter(delta::MailboxObject& mbx, uint64_t msg,
                                  std::vector<int>& ran, int id) {
  co_await delta::MailboxPutAwaiter{mbx, msg};
  ran.push_back(id);
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

TEST(IpcSync, MailboxMultipleGetPutCycles) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 100; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 100);
  for (uint64_t i = 0; i < 100; ++i) {
    uint64_t msg = 0;
    EXPECT_EQ(mb.TryGet(msg), 1);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
}

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
  EXPECT_FALSE(mb.IsFull());
}

TEST(IpcSync, MailboxParameterizedTypeValues) {
  MailboxObject mb;

  mb.TryPut(0xDEADBEEF);
  mb.TryPut(0xCAFEBABE);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xDEADBEEFu);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 0xCAFEBABEu);
}

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

TEST(IpcSync, MailboxDefaultConstructorUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.bound, 0);
  EXPECT_EQ(mb.Num(), 0);
  EXPECT_FALSE(mb.IsFull());
}

TEST(IpcSync, MailboxBoundedPutRejectedWhenFull) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(42), 1);
  EXPECT_EQ(mb.TryPut(99), 0);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4: a process placing a message into a full mailbox shall be suspended
// until enough room becomes available. The mailbox (bound 1) is filled, so the
// putter blocks — its message is not stored and the process stays parked on the
// put-waiter queue. Only when a get() removes the existing message does room
// open up; WakePutWaiters() then resumes the putter, which stores its message.
TEST(IpcSync, MailboxFullPutSuspendsSenderUntilRoomAvailable) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(1), MbxPutStatus::kPlaced);  // mailbox now full

  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 2, ran, 7);
  putter.h.resume();  // runs to the co_await; full -> parks, message not stored
  ASSERT_EQ(mb.put_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(mb.Num(), 1);

  uint64_t msg = 0;
  // Removing the stored message frees a slot and wakes the parked putter.
  ASSERT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 1u);         // FIFO: the originally stored message exits first
  ASSERT_EQ(ran.size(), 1u);  // the suspended sender resumed
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.put_waiters.empty());
  EXPECT_EQ(mb.Num(), 1);  // putter's deferred message is now stored

  ASSERT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 2u);

  putter.h.destroy();
}

// §15.4: unbounded mailboxes never suspend a thread in a send operation. The
// putter targets an unbounded mailbox, so the put completes immediately on the
// ready path — it never parks on the put-waiter queue and runs to completion at
// the first resume().
TEST(IpcSync, MailboxUnboundedPutNeverSuspendsSender) {
  MailboxObject mb;  // bound 0 -> unbounded
  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 0xABC, ran, 3);
  putter.h.resume();  // never full -> stores immediately, no suspension

  EXPECT_TRUE(mb.put_waiters.empty());
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 3);
  EXPECT_EQ(mb.Num(), 1);
  uint64_t msg = 0;
  ASSERT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xABCu);

  putter.h.destroy();
}

}
