#include <gtest/gtest.h>

#include <coroutine>
#include <cstdint>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

uint64_t Word(const Logic4Snapshot& msg) { return msg.Get().ToUint64(); }

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
                                  std::vector<int>& ran, int id,
                                  SimContext* ctx = nullptr) {
  co_await MailboxPutAwaiter{mbx, Msg(msg), {}, false, ctx};
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

TEST(IpcSync, MailboxPutAfterBlockAppendsAtTail) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(20).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(Msg(30).Get()), MbxPutStatus::kBlock);
  EXPECT_EQ(mb.Num(), 2);

  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 10u);
  EXPECT_EQ(mb.Put(Msg(30).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 2);

  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 20u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 30u);
}

TEST(IpcSync, MailboxPutSuspendsWhenFullThenResumesWhenRoomFrees) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  EXPECT_TRUE(mb.IsFull());

  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 20, ran, 7);
  putter.h.resume();
  ASSERT_EQ(mb.put_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(mb.Num(), 1);

  Logic4Snapshot got;
  EXPECT_EQ(mb.Get(got), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(got), 10u);

  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.put_waiters.empty());
  EXPECT_EQ(mb.Num(), 1);
  Logic4Snapshot tail;
  EXPECT_EQ(mb.Get(tail), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(tail), 20u);

  putter.h.destroy();
}

TEST(IpcSync, MailboxPutParkedOutsideAProcessResumesWhenRoomFrees) {
  SimFixture f;
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(Msg(10).Get()), MbxPutStatus::kPlaced);
  std::vector<int> ran;
  auto putter = SpawnPutter(mb, 20, ran, 3, &f.ctx);
  putter.h.resume();
  ASSERT_EQ(mb.put_waiters.size(), 1u);
  Logic4Snapshot got;
  EXPECT_EQ(mb.Get(got), MbxGetStatus::kRetrieved);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 3);
  Logic4Snapshot tail;
  EXPECT_EQ(mb.Get(tail), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(tail), 20u);
  putter.h.destroy();
}

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
