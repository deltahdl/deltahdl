#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// Minimal getter coroutine used to observe the get-side wakeup. It starts
// suspended; the first resume runs it to the co_await, where — while the
// mailbox is empty — the awaiter parks the handle on the mailbox's get-waiter
// queue. A later put() that places a message resumes it through production
// WakeGetWaiters(), at which point it retrieves the message and records that it
// ran. Parking on get_waiters is exactly what a get awaiter's suspend does; the
// rule under observation here is the resume performed by WakeGetWaiters().
struct GetWaiter {
  MailboxObject& mbx;
  bool await_ready() { return !mbx.messages.empty(); }
  void await_suspend(std::coroutine_handle<> h) {
    mbx.get_waiters.push_back(h);
  }
  void await_resume() const noexcept {}
};

struct BlockingGetter {
  struct promise_type {
    BlockingGetter get_return_object() {
      return BlockingGetter{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
  std::coroutine_handle<promise_type> h;
};

inline BlockingGetter SpawnGetter(MailboxObject& mbx, uint64_t& out,
                                  std::vector<int>& ran, int id) {
  co_await GetWaiter{mbx};
  mbx.Get(out);
  ran.push_back(id);
}

TEST(IpcSync, MailboxGetRetrievesFrontMessage) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxGetEmptyReturnsBlock) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: a get() on an empty mailbox blocks the current process until a
// message is placed in the mailbox. The getter parks while the mailbox is empty
// and is resumed only once a put() supplies a message, after which it retrieves
// that message.
TEST(IpcSync, MailboxGetBlocksUntilMessagePlaced) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  uint64_t got = 0;
  auto getter = SpawnGetter(mb, got, ran, 9);
  getter.h.resume();  // runs to the co_await; empty -> parks on get_waiters
  ASSERT_EQ(mb.get_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  // Placing a message wakes the parked getter via WakeGetWaiters().
  EXPECT_EQ(mb.TryPut(0x55), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 9);
  EXPECT_TRUE(mb.get_waiters.empty());
  EXPECT_EQ(got, 0x55u);   // the resumed getter retrieved the placed message
  EXPECT_EQ(mb.Num(), 0);  // and consumed it from the queue

  getter.h.destroy();
}

// §15.4.5: the mailbox waiting queue is FIFO — the arrival order of processes
// blocked in get() shall be preserved. Two getters park on an empty mailbox in
// arrival order; each subsequent put() wakes the earliest-arrived waiter first,
// so the first getter retrieves the first placed message and the second getter
// the second. This observes production WakeGetWaiters() servicing get_waiters
// from the front.
TEST(IpcSync, MailboxWaitingQueuePreservesArrivalOrder) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  uint64_t got_first = 0;
  uint64_t got_second = 0;
  auto first = SpawnGetter(mb, got_first, ran, 1);
  auto second = SpawnGetter(mb, got_second, ran, 2);
  first.h.resume();   // parks first on get_waiters
  second.h.resume();  // parks second behind it
  ASSERT_EQ(mb.get_waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  // Each placed message wakes exactly the head of the waiting queue.
  EXPECT_EQ(mb.TryPut(0xAA), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);  // the earliest arrival ran first
  EXPECT_EQ(got_first, 0xAAu);

  EXPECT_EQ(mb.TryPut(0xBB), 1);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);  // the later arrival ran second
  EXPECT_EQ(got_second, 0xBBu);
  EXPECT_TRUE(mb.get_waiters.empty());

  first.h.destroy();
  second.h.destroy();
}

TEST(IpcSync, MailboxGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  mb.TryPut(300);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 200u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 300u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
}

TEST(IpcSync, MailboxGetFreesSpaceForPut) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

// Arbitrary, distinct type ids standing in for two non-equivalent data types.
constexpr uint32_t kTypeInt = 1;
constexpr uint32_t kTypeString = 2;

// §15.4.5: the mailbox maintains the data type placed by put(), so a get()
// whose variable type matches that stored type retrieves the value.
TEST(IpcSync, MailboxGetMaintainsTypePlacedByPut) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: a single (typeless) mailbox can carry messages of different types,
// and the implementation maintains the type placed by each put() individually.
// Two messages with distinct stored types coexist in the queue; each get()
// checks the type of the specific (front) message it retrieves, so a get()
// whose variable type matches the front message succeeds while the other stored
// type waits its turn and is then retrieved by a get() of its own matching
// type.
TEST(IpcSync, MailboxGetRetrievesEachMessageWithItsOwnStoredType) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);     // first placed, first out
  mb.TryPut(0xCD, kTypeString);  // second placed, second out
  uint64_t msg = 0;

  // The front message was placed as kTypeInt: a kTypeString get() sees the
  // front's maintained type, not the later kTypeString message, and errors.
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  EXPECT_EQ(mb.Num(), 2);

  // Retrieved by its own stored type; the queue then advances to the second.
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xABu);
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xCDu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: when the variable type is not equivalent to the stored message type,
// a run-time type error is generated instead of a retrieval.
TEST(IpcSync, MailboxGetTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  // The errored get() does not consume the message and does not clobber msg.
  EXPECT_EQ(msg, 0u);
  EXPECT_EQ(mb.Num(), 1);
}

}  // namespace
