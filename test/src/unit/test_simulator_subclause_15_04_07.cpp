#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// A 64-bit two-state message holding `v`, as the C++ cases below place one,
// and the low word of a message read back out of the queue.
Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

uint64_t Word(const Logic4Snapshot& msg) { return msg.Get().ToUint64(); }

// Two non-equivalent message types, §6.22.2 c)'s int and §6.22.1 a)'s string.
constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

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

inline BlockingTask SpawnPeeker(MailboxObject& mbx, Logic4Snapshot& out,
                                std::vector<int>& ran, int id) {
  co_await PeekWaiter{mbx};
  mbx.Peek(out);
  ran.push_back(id);
}

inline BlockingTask SpawnGetter(MailboxObject& mbx, Logic4Snapshot& out,
                                std::vector<int>& ran, int id) {
  co_await GetWaiter{mbx};
  mbx.Get(out);
  ran.push_back(id);
}

TEST(IpcSync, MailboxPeekCopiesWithoutRemoving) {
  MailboxObject mb;
  mb.TryPut(Msg(42).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxPeekEmptyReturnsBlock) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kBlock);
}

TEST(IpcSync, MailboxPeekRepeatedReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(Msg(100).Get());
  mb.TryPut(Msg(200).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 100u);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 100u);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxPeekThenGetReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(Msg(55).Get());
  Logic4Snapshot peek_msg;
  Logic4Snapshot get_msg;
  EXPECT_EQ(mb.Peek(peek_msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(mb.Get(get_msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(peek_msg), Word(get_msg));
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxPeekAfterGetReturnsNext) {
  MailboxObject mb;
  mb.TryPut(Msg(10).Get());
  mb.TryPut(Msg(20).Get());
  Logic4Snapshot msg;
  mb.Get(msg);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 20u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: when the receiving variable's type is not equivalent to the type of
// the message in the mailbox, peek() generates a run-time type error instead of
// copying. The message is left untouched in the queue and the variable is not
// clobbered.
TEST(IpcSync, MailboxPeekTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xEE);
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(Word(msg), 0xEEu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: a peek() that reported a type error left the message in place, so a
// later peek() with the matching type still copies it.
TEST(IpcSync, MailboxPeekTypeErrorLeavesMessageForMatchingPeek) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(mb.Peek(msg, kTypeInt), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: a peek() on an empty mailbox blocks the current process until a
// message is placed. The peeker parks while empty and is resumed only once a
// put() supplies a message; because peek does not remove it, the message
// remains in the queue afterward.
TEST(IpcSync, MailboxPeekBlocksUntilMessagePlaced) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  Logic4Snapshot got;
  auto peeker = SpawnPeeker(mb, got, ran, 7);
  peeker.h.resume();  // runs to the co_await; empty -> parks on peek_waiters
  ASSERT_EQ(mb.peek_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  // Wakes the parked peeker via WakeGetWaiters().
  EXPECT_EQ(mb.TryPut(Msg(0x55).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_EQ(Word(got), 0x55u);  // the resumed peeker copied the placed message
  EXPECT_EQ(mb.Num(), 1);       // and left it in the queue

  peeker.h.destroy();
}

// §15.4.7: a single placed message can unblock more than one process. As long
// as a message remains in the queue, every process blocked in peek() or get()
// becomes unblocked — the peekers copy the message (leaving it in place) and a
// getter then removes it.
TEST(IpcSync, MailboxOneMessageUnblocksMultiplePeekersAndGetter) {
  MailboxObject mb;  // empty
  std::vector<int> ran;
  Logic4Snapshot p1, p2, g;
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
  EXPECT_EQ(mb.TryPut(Msg(0x77).Get()), 1);
  EXPECT_EQ(ran.size(), 3u);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_TRUE(mb.get_waiters.empty());
  EXPECT_EQ(Word(p1), 0x77u);  // both peekers copied the same message...
  EXPECT_EQ(Word(p2), 0x77u);
  EXPECT_EQ(Word(g), 0x77u);  // ...and the getter retrieved it
  EXPECT_EQ(mb.Num(), 0);     // only the getter removed it from the queue

  peeker1.h.destroy();
  peeker2.h.destroy();
  getter.h.destroy();
}

// §15.4.7 (printed page 376): peek() copies one message from the mailbox
// without removing it, so the copy reads 4 and num() still counts the one
// message: 41. A peek() that removed the message would have read 40.
TEST(MailboxSim, PeekCopiesWithoutRemoving) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, r;\n"
      "  initial begin\n"
      "    mb.put(4);\n"
      "    mb.peek(x);\n"
      "    r = x * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 41u);
}

// §15.4.7 (printed page 376): peek() on an empty mailbox blocks the process
// until a message is placed, and the message stays in the queue for the
// get() that follows, so the peeked 6 at time 2 and a num() of 1 read as
// 621. A peek() that did not wait would have stored nothing and read the
// time as 0.
TEST(MailboxSim, PeekWaitsUntilAMessageIsPlaced) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, r;\n"
      "  initial begin\n"
      "    mb.peek(x);\n"
      "    r = x * 100 + $time * 10 + mb.num();\n"
      "  end\n"
      "  initial #2 mb.put(6);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 621u);
}

// §15.4.7 (printed page 376): when the type of the message variable is not
// equivalent to the type of the message in the mailbox, peek() generates a
// run-time error. The typeless mailbox holds the real 2.5, and peek() into
// an int is reported at the variable and leaves the int as it was: 9. An
// untyped copy stored the low word of the real's bit pattern over the 9.
TEST(MailboxSim, PeekIntoAVariableOfAnotherTypeIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x = 9;\n"
      "  initial begin\n"
      "    mb.put(2.5);\n"
      "    mb.peek(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "mailbox peek(): the message's type is not equivalent to the type of 'x'",
      6, "15.4.7"));
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

// §15.4.5 (printed page 376) has get() suspend the process only while the
// mailbox is empty, and §13.4 (printed 340) forbids a function to suspend
// the process enabling it, so a get() a void function reaches on a mailbox
// holding a message removes it where it stands: 4 and a num() of 0 read as
// 40. Served by the expression evaluator, which answers num() and the try_*
// forms alone, the function's get() retrieved nothing and read 1.
TEST(MailboxSim, GetInsideAFunctionRetrievesAHeldMessage) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  mailbox mb = new;\n"
                      "  int x, r;\n"
                      "  function void g();\n"
                      "    mb.get(x);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    mb.put(4);\n"
                      "    g();\n"
                      "    r = x * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            40u);
}

// §15.4.7 (printed page 376) has peek() copy the front message and leave it
// in the queue, suspending the process only while the mailbox is empty, so a
// peek() a void function reaches on a mailbox holding a message copies it
// where it stands (§13.4, printed 340): 4 and a num() of 1 read as 41. The
// function's peek() copied nothing and read 1.
TEST(MailboxSim, PeekInsideAFunctionCopiesAHeldMessage) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  mailbox mb = new;\n"
                      "  int y, r;\n"
                      "  function void pk();\n"
                      "    mb.peek(y);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    mb.put(4);\n"
                      "    pk();\n"
                      "    r = y * 10 + mb.num();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            41u);
}

// §13.4 (printed page 340) with §15.4.5 (printed 376): a get() on an empty
// mailbox would suspend the process, which a function may not do, so the
// function's get() is the error, reported at the call under §13.4 with the
// variable as it was, 9, and the process going on to read num() 0 plus 1.
// The function's get() of an empty mailbox raised nothing.
TEST(MailboxSim, GetInsideAFunctionOfAnEmptyMailboxIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x = 9, n;\n"
      "  function void g();\n"
      "    mb.get(x);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    g();\n"
      "    n = mb.num() + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "mailbox get(): 'mb' is empty, so the call would "
                            "block inside a function",
                            5, "13.4"));
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 1u);
}

}  // namespace
