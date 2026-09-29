#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/awaiters.h"
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
  co_await MailboxPutAwaiter{mbx, Msg(msg), {}};
  ran.push_back(id);
}

TEST(IpcSync, MailboxPutUnboundedAlwaysPlaced) {
  MailboxObject mb;
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(20).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(30).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 3);
}

TEST(IpcSync, MailboxPutFifoOrder) {
  MailboxObject mb;
  mb.Put(Msg(100).Get());
  mb.Put(Msg(200).Get());
  mb.Put(Msg(300).Get());
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 100u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 200u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 300u);
}

// §15.4.3: a put() blocked on a full bounded mailbox stores nothing while it
// waits, and once room frees the message joins the queue in strict FIFO order
// — at the tail, behind a message that is already enqueued. With a second
// message still present when the slot opens, draining must yield the older
// message first and the once-blocked message last.
TEST(IpcSync, MailboxPutAfterBlockAppendsAtTail) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(20).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(30).Get()), MbxPutStatus::kBlock);  // full: not stored
  EXPECT_EQ(mb.Num(), 2);

  Logic4Snapshot msg;
  mb.TryGet(msg);  // frees a slot, removes 10
  EXPECT_EQ(Word(msg), 10u);
  // Now stored, at the tail.
  EXPECT_EQ(mb.Put(Msg(30).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 2);

  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 20u);  // the message queued ahead exits first
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 30u);  // the once-blocked message exits last
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
  // Fills the single slot.
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  EXPECT_TRUE(mb.IsFull());

  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 20, ran, 7);
  putter.h.resume();  // runs to the co_await; full -> parks on put_waiters
  ASSERT_EQ(mb.put_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(mb.Num(), 1);  // the suspended put has stored nothing yet

  // A get() removes a message and frees a slot, resuming the parked sender via
  // WakePutWaiters().
  Logic4Snapshot got;
  EXPECT_EQ(mb.Get(got), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(got), 10u);

  // The resumed awaiter stored the once-blocked message and the sender ran.
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.put_waiters.empty());
  EXPECT_EQ(mb.Num(), 1);
  Logic4Snapshot tail;
  EXPECT_EQ(mb.Get(tail), MbxGetStatus::kRetrieved);
  // The message that had to wait is now in the queue.
  EXPECT_EQ(Word(tail), 20u);

  putter.h.destroy();
}

// §15.4.3 (printed page 375): put() on a mailbox created with a bounded queue
// suspends the process until there is enough room in the queue. The queue of
// one holds the first message, so the forked put(2) waits, and the get() at
// time 5 in the other branch is what makes room: it retrieves the 1 that was
// placed first and the waiting put() completes at time 5, so 1 and 5 read as
// 15. A put() that did not wait would have recorded time 0.
TEST(MailboxSim, PutWaitsForRoomInABoundedQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new(1);\n"
      "  int got, at, r;\n"
      "  initial begin\n"
      "    mb.put(1);\n"
      "    fork\n"
      "      begin\n"
      "        mb.put(2);\n"
      "        at = $time;\n"
      "      end\n"
      "      #5 mb.get(got);\n"
      "    join\n"
      "    r = got * 10 + at;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §15.4.3 with §8.12: `b = a` leaves one mailbox under both names, so the
// message b.put() places is the one a.get() retrieves, and the two handles
// compare equal while an unassigned one is null: 4, then 1, 0 and 1, read as
// 4101. b's name kept a mailbox of its own, so a.get() waited for ever and r
// was never written.
TEST(MailboxSim, PutThroughAHandleCopiedAtModuleScopeReachesTheMailbox) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox a = new;\n"
      "  mailbox b, c;\n"
      "  int v, r;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    b.put(4);\n"
      "    a.get(v);\n"
      "    r = v * 1000 + (a == b) * 100 + (b == null) * 10 + (c == null);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4101u);
}

// §15.4.3 with §23.6 and §27.5: a mailbox a named generate block declares is
// reached from outside the block by the path through it, `g.mb`, so the
// message put there is the one the block's own get() retrieves: 7, read as 7.
// The path reached no mailbox, and the block's get() waited for ever.
TEST(MailboxSim, PutThroughAGenerateBlockPathReachesTheBlocksMailbox) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  if (1) begin : g\n"
      "    mailbox mb = new;\n"
      "    initial begin int v; mb.get(v); r = v; end\n"
      "  end\n"
      "  initial #1 g.mb.put(7);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §15.4.3 with §7.8 and §7.10: a queue and an associative array of mailboxes
// hold handles, so put() and get() on an element act on the mailbox that
// element refers to: q[0] and q[1], each built by its own `new`, give back
// 7 and 8, and m["a"] and m["b"] 3 and 4, with m["a"] then empty: 7, 8, 3,
// 4 and 0, read as 78340. The elements named no mailbox and every get()
// left its target at 0.
TEST(MailboxSim, ElementsOfContainersOfMailboxesHoldTheirQueues) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox q[$];\n"
      "  mailbox m[string];\n"
      "  mailbox t;\n"
      "  int v0, v1, a, b, r;\n"
      "  initial begin\n"
      "    t = new; q.push_back(t);\n"
      "    t = new; q.push_back(t);\n"
      "    m[\"a\"] = new; m[\"b\"] = new;\n"
      "    q[0].put(7); q[1].put(8);\n"
      "    m[\"a\"].put(3); m[\"b\"].put(4);\n"
      "    q[0].get(v0); q[1].get(v1);\n"
      "    m[\"a\"].get(a); m[\"b\"].get(b);\n"
      "    r = v0 * 10000 + v1 * 1000 + a * 100 + b * 10 + m[\"a\"].num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 78340u);
}

}  // namespace
