#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "simulator/awaiters.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// Minimal coroutine modelling a process that blocks in mailbox put(). It starts
// suspended; the first resume() runs it up to the co_await on the production
// MailboxPutAwaiter, which either stores the message immediately or — when the
// bounded mailbox is full — parks the handle on the mailbox's put-waiter queue
// without storing anything. Once a get() frees a slot, production
// WakePutWaiters() resumes it; the awaiter then stores the deferred message and
// the body records its id, so the sequence of events reveals when the suspended
// sender actually completed.
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

inline BlockingPutter SpawnPutter(MailboxObject& mbx, uint64_t msg,
                                  std::vector<int>& ran, int id) {
  co_await MailboxPutAwaiter{mbx, msg};
  ran.push_back(id);
}

TEST(IpcSync, MailboxPutUnboundedAlwaysPlaced) {
  MailboxObject mb;
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(20), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 3);
}

TEST(IpcSync, MailboxPutFifoOrder) {
  MailboxObject mb;
  mb.Put(100);
  mb.Put(200);
  mb.Put(300);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 100u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 200u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 300u);
}

// §15.4.3: a put() blocked on a full bounded mailbox stores nothing while it
// waits, and once room frees the message joins the queue in strict FIFO order
// — at the tail, behind a message that is already enqueued. With a second
// message still present when the slot opens, draining must yield the older
// message first and the once-blocked message last.
TEST(IpcSync, MailboxPutAfterBlockAppendsAtTail) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(20), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kBlock);  // full: not stored
  EXPECT_EQ(mb.Num(), 2);

  uint64_t msg = 0;
  mb.TryGet(msg);  // frees a slot, removes 10
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kPlaced);  // now stored, at the tail
  EXPECT_EQ(mb.Num(), 2);

  mb.TryGet(msg);
  EXPECT_EQ(msg, 20u);  // the message queued ahead exits first
  mb.TryGet(msg);
  EXPECT_EQ(msg, 30u);  // the once-blocked message exits last
}

// §15.4.3: when the mailbox was created with a bounded queue and is full, a
// put() shall suspend the process until there is enough room in the queue. This
// drives the actual suspend/resume through the production MailboxPutAwaiter: on
// a full mailbox the awaiter parks the sender on put_waiters and stores
// nothing, and only a get() that frees a slot resumes it — through production
// WakePutWaiters() — at which point the deferred message joins the queue and
// the sender continues.
TEST(IpcSync, MailboxPutSuspendsWhenFullThenResumesWhenRoomFrees) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);  // fills the single slot
  EXPECT_TRUE(mb.IsFull());

  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 20, ran, 7);
  putter.h.resume();  // runs to the co_await; full -> parks on put_waiters
  ASSERT_EQ(mb.put_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(mb.Num(), 1);  // the suspended put has stored nothing yet

  // A get() removes a message and frees a slot, resuming the parked sender via
  // WakePutWaiters().
  uint64_t got = 0;
  EXPECT_EQ(mb.Get(got), MbxGetStatus::kRetrieved);
  EXPECT_EQ(got, 10u);

  // The resumed awaiter stored the once-blocked message and the sender ran.
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.put_waiters.empty());
  EXPECT_EQ(mb.Num(), 1);
  uint64_t tail = 0;
  EXPECT_EQ(mb.Get(tail), MbxGetStatus::kRetrieved);
  EXPECT_EQ(tail, 20u);  // the message that had to wait is now in the queue

  putter.h.destroy();
}

}  // namespace
