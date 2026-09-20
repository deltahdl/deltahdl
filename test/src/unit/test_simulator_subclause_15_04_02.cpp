#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// A 64-bit two-state message holding `v`, as the C++ cases below place one.
Logic4Snapshot Msg(uint64_t v) {
  Logic4Word word{v, 0};
  Logic4Vec vec{64, 1, &word};
  Logic4Snapshot snap;
  snap.Capture(vec);
  return snap;
}

TEST(IpcSync, MailboxNumReflectsState) {
  delta::MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  mb.TryPut(Msg(1).Get());
  EXPECT_EQ(mb.Num(), 1);
  mb.TryPut(Msg(2).Get());
  EXPECT_EQ(mb.Num(), 2);
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxNumAtBound) {
  delta::MailboxObject mb(3);
  mb.TryPut(Msg(1).Get());
  mb.TryPut(Msg(2).Get());
  mb.TryPut(Msg(3).Get());
  EXPECT_EQ(mb.Num(), 3);
  EXPECT_EQ(mb.TryPut(Msg(4).Get()), 0);
  EXPECT_EQ(mb.Num(), 3);
}

// num() reports the live message count. A retrieval attempt on an empty
// mailbox removes nothing, so num() must keep reporting zero rather than
// underflowing — the read-side mirror of the at-bound put case above.
TEST(IpcSync, MailboxNumUnchangedByFailedGet) {
  delta::MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.2 (printed page 375): num() returns the number of messages in the
// mailbox at the moment it is asked, so it reads 2 after two put() calls and
// 1 after a get() has removed one: 21. Left unlowered, the num() calls
// evaluated to nothing and r read x.
TEST(MailboxSim, NumCountsTheMessagesInTheQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int a, before, after, r;\n"
      "  initial begin\n"
      "    mb.put(1);\n"
      "    mb.put(2);\n"
      "    before = mb.num();\n"
      "    mb.get(a);\n"
      "    after = mb.num();\n"
      "    r = before * 10 + after;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

}  // namespace
