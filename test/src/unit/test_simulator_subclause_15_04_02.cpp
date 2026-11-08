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

TEST(IpcSync, MailboxNumUnchangedByFailedGet) {
  delta::MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  Logic4Snapshot msg;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(MailboxSim, NumCountsTheMessagesInTheQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int a, held, left, r;\n"
      "  initial begin\n"
      "    mb.put(1);\n"
      "    mb.put(2);\n"
      "    held = mb.num();\n"
      "    mb.get(a);\n"
      "    left = mb.num();\n"
      "    r = held * 10 + left;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 21u);
}

}  // namespace
