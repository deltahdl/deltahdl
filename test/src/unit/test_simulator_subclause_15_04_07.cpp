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

Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

uint64_t Word(const Logic4Snapshot& msg) { return msg.Get().ToUint64(); }

constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

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

TEST(IpcSync, MailboxPeekTypeMismatchGeneratesError) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xEE);
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(Word(msg), 0xEEu);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxPeekTypeErrorLeavesMessageForMatchingPeek) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg, kTypeString), MbxPeekStatus::kTypeError);
  EXPECT_EQ(mb.Peek(msg, kTypeInt), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxPeekBlocksUntilMessagePlaced) {
  MailboxObject mb;
  std::vector<int> ran;
  Logic4Snapshot got;
  auto peeker = SpawnPeeker(mb, got, ran, 7);
  peeker.h.resume();
  ASSERT_EQ(mb.peek_waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  EXPECT_EQ(mb.TryPut(Msg(0x55).Get()), 1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 7);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_EQ(Word(got), 0x55u);
  EXPECT_EQ(mb.Num(), 1);

  peeker.h.destroy();
}

TEST(IpcSync, MailboxOneMessageUnblocksMultiplePeekersAndGetter) {
  MailboxObject mb;
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

  EXPECT_EQ(mb.TryPut(Msg(0x77).Get()), 1);
  EXPECT_EQ(ran.size(), 3u);
  EXPECT_TRUE(mb.peek_waiters.empty());
  EXPECT_TRUE(mb.get_waiters.empty());
  EXPECT_EQ(Word(p1), 0x77u);
  EXPECT_EQ(Word(p2), 0x77u);
  EXPECT_EQ(Word(g), 0x77u);
  EXPECT_EQ(mb.Num(), 0);

  peeker1.h.destroy();
  peeker2.h.destroy();
  getter.h.destroy();
}

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
