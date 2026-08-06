#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// Arbitrary, distinct type ids standing in for two non-equivalent data types.
constexpr uint32_t kTypeInt = 1;
constexpr uint32_t kTypeString = 2;

// Minimal coroutine helpers used to observe the suspend/resume side of peek()
// and get(). Each starts suspended; the first resume runs it to the co_await,
// where — while the mailbox is empty — the awaiter parks the handle on the
// relevant waiter queue. A later put() resumes the parked handles through
// production WakeGetWaiters(): all peek waiters first (peek never consumes, so
// the message remains), then one get waiter. The rule under observation is the
// resume that WakeGetWaiters() performs, not the parking itself.
struct PeekWaiter {
  MailboxObject& mbx;
  bool await_ready() { return !mbx.messages.empty(); }
  void await_suspend(std::coroutine_handle<> h) {
    mbx.peek_waiters.push_back(h);
  }
  void await_resume() const noexcept {}
};

struct GetWaiter {
  MailboxObject& mbx;
  bool await_ready() { return !mbx.messages.empty(); }
  void await_suspend(std::coroutine_handle<> h) {
    mbx.get_waiters.push_back(h);
  }
  void await_resume() const noexcept {}
};

struct BlockingTask {
  struct promise_type {
    BlockingTask get_return_object() {
      return BlockingTask{
          std::coroutine_handle<promise_type>::from_promise(*this)};
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void return_void() {}
    void unhandled_exception() {}
  };
  std::coroutine_handle<promise_type> h;
};

inline BlockingTask SpawnPeeker(MailboxObject& mbx, uint64_t& out,
                                std::vector<int>& ran, int id) {
  co_await PeekWaiter{mbx};
  mbx.Peek(out);
  ran.push_back(id);
}

inline BlockingTask SpawnGetter(MailboxObject& mbx, uint64_t& out,
                                std::vector<int>& ran, int id) {
  co_await GetWaiter{mbx};
  mbx.Get(out);
  ran.push_back(id);
}

TEST(IpcSync, MailboxPeekCopiesWithoutRemoving) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxPeekEmptyReturnsBlock) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kBlock);
}

TEST(IpcSync, MailboxPeekRepeatedReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxPeekThenGetReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(55);
  uint64_t peek_msg = 0;
  uint64_t get_msg = 0;
  EXPECT_EQ(mb.Peek(peek_msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(mb.Get(get_msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(peek_msg, get_msg);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxPeekAfterGetReturnsNext) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  uint64_t msg = 0;
  mb.Get(msg);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 20u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: when the receiving variable's type is not equivalent to the type of
// the message in the mailbox, peek() generates a run-time type error instead of
// copying. The message is left untouched in the queue and the variable is not
// clobbered.
TEST(IpcSync, MailboxPeekTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(msg, 0u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: a peek() that reported a type error left the message in place, so a
// later peek() with the matching type still copies it.
TEST(IpcSync, MailboxPeekTypeErrorLeavesMessageForMatchingPeek) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(mb.Peek(msg, kTypeInt), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: a peek() on an empty mailbox blocks the current process until a
// message is placed. The peeker parks while empty and is resumed only once a
// put() supplies a message; because peek does not remove it, the message
// remains in the queue afterward.
TEST(IpcSync, MailboxPeekBlocksUntilMessagePlaced) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  uint64_t got = 0;
  auto peeker = SpawnPeeker(mb, got, ran, 7);
  peeker.h.resume();  // runs to the co_await; empty -> parks on peek_waiters
  ASSERT_EQ(mb.peek_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  EXPECT_EQ(mb.TryPut(0x55),
            1);  // wakes the parked peeker via WakeGetWaiters()
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_EQ(got, 0x55u);   // the resumed peeker copied the placed message
  EXPECT_EQ(mb.Num(), 1);  // and left it in the queue

  peeker.h.destroy();
}

// §15.4.7: a single placed message can unblock more than one process. As long
// as a message remains in the queue, every process blocked in peek() or get()
// becomes unblocked — the peekers copy the message (leaving it in place) and a
// getter then removes it.
TEST(IpcSync, MailboxOneMessageUnblocksMultiplePeekersAndGetter) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  uint64_t p1 = 0, p2 = 0, g = 0;
  auto peeker1 = SpawnPeeker(mb, p1, ran, 1);
  auto peeker2 = SpawnPeeker(mb, p2, ran, 2);
  auto getter = SpawnGetter(mb, g, ran, 3);
  peeker1.h.resume();
  peeker2.h.resume();
  getter.h.resume();
  ASSERT_EQ(mb.peek_waiters.size(), 2u);
  ASSERT_EQ(mb.get_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  // One message wakes both blocked peekers and the blocked getter.
  EXPECT_EQ(mb.TryPut(0x77), 1);
  EXPECT_EQ(ran.size(), 3u);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_TRUE(mb.get_waiters.empty());
  EXPECT_EQ(p1, 0x77u);  // both peekers copied the same message...
  EXPECT_EQ(p2, 0x77u);
  EXPECT_EQ(g, 0x77u);     // ...and the getter retrieved it
  EXPECT_EQ(mb.Num(), 0);  // only the getter removed it from the queue

  peeker1.h.destroy();
  peeker2.h.destroy();
  getter.h.destroy();
}

}  // namespace
