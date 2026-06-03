#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// Minimal getter coroutine used to observe the get-side wakeup. It starts
// suspended; the first resume runs it to the co_await, where — while the mailbox
// is empty — the awaiter parks the handle on the mailbox's get-waiter queue. A
// later put() that places a message resumes it through production
// WakeGetWaiters(), at which point it retrieves the message and records that it
// ran. Parking on get_waiters is exactly what a get awaiter's suspend does; the
// rule under observation here is the resume performed by WakeGetWaiters().
struct GetWaiter {
  MailboxObject& mbx;
  bool await_ready() { return !mbx.messages.empty(); }
  void await_suspend(std::coroutine_handle<> h) { mbx.get_waiters.push_back(h); }
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

TEST(IpcSync, MailboxGetDrainsMailbox) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 50; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 50);
  for (uint64_t i = 0; i < 50; ++i) {
    uint64_t msg = 0;
    EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
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

// §15.4.5: a get() that reported a type error leaves the message in the queue,
// so a subsequent get() with the matching type still retrieves it.
TEST(IpcSync, MailboxGetTypeErrorLeavesMessageForMatchingGet) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg, kTypeString), MbxGetStatus::kTypeError);
  EXPECT_EQ(mb.Get(msg, kTypeInt), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 0xABu);
}

}
