#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
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

TEST(IpcSync, MailboxTryPutBoundedWithRoom) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(Msg(10).Get()), 1);
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 1);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutRejectsAtBoundGreaterThanOne) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(Msg(10).Get()), 1);
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 1);
  EXPECT_EQ(mb.TryPut(Msg(30).Get()), 0);
  EXPECT_EQ(mb.Num(), 2);
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 10u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 20u);
}

TEST(IpcSync, MailboxTryPutFifoOrder) {
  MailboxObject mb;
  mb.TryPut(Msg(100).Get());
  mb.TryPut(Msg(200).Get());
  mb.TryPut(Msg(300).Get());
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 100u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 200u);
  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 300u);
}

TEST(IpcSync, MailboxTryPutUnboundedNeverFull) {
  MailboxObject mb;
  for (int i = 0; i < 100; ++i) {
    EXPECT_EQ(mb.TryPut(Msg(static_cast<uint64_t>(i)).Get()), 1);
  }
  EXPECT_EQ(mb.Num(), 100);
}

TEST(IpcSync, MailboxTryPutSucceedsAfterGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(Msg(10).Get()), 1);
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 0);
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(mb.TryPut(Msg(30).Get()), 1);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(MailboxSim, TryPutAnswersZeroOnAFullQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new(1);\n"
      "  int first, second, r;\n"
      "  initial begin\n"
      "    first = mb.try_put(5);\n"
      "    second = mb.try_put(6);\n"
      "    r = first * 100 + second * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 101u);
}

TEST(MailboxSim, ClassExtendingTheMailboxHoldsTheBaseQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class LogMbx extends mailbox;\n"
      "    int sent;\n"
      "    function new(int b = 0); super.new(b); sent = 0; endfunction\n"
      "    function void send(int x); void'(try_put(x)); sent++; endfunction\n"
      "  endclass\n"
      "  LogMbx m;\n"
      "  int v, r;\n"
      "  initial begin\n"
      "    m = new;\n"
      "    m.send(6); m.send(7);\n"
      "    m.get(v);\n"
      "    r = m.sent * 10 + v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 26u);
}

TEST(IpcSync, MethodsOfASyncPropertyReachedThroughACallsResult) {
  SimFixture f;
  auto out = RunCapture(
      "class K;\n"
      "  mailbox #(int) mb = new;\n"
      "  semaphore s = new(2);\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, x, n, ok;\n"
      "  K k = new;\n"
      "  function K pk(); calls++; return k; endfunction\n"
      "  initial begin\n"
      "    ok = pk().mb.try_put(5);\n"
      "    n = pk().mb.num();\n"
      "    ok += pk().mb.try_get(x);\n"
      "    pk().s.put(1);\n"
      "    ok += pk().s.try_get(3);\n"
      "    $display(\"%0d %0d %0d %0d\", calls, ok, n, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 3 1 5\n");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
