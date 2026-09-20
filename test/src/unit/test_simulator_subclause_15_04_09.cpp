#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
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

TEST(IpcSync, MailboxParameterizedSameMethodsAsDynamic) {
  MailboxObject mb;

  EXPECT_EQ(mb.Num(), 0);
  EXPECT_EQ(mb.Put(Msg(42).Get()), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.TryPut(Msg(43).Get()), 1);
  EXPECT_EQ(mb.Num(), 2);

  Logic4Snapshot msg;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(Word(msg), 43u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxParameterizedSameRuntimeAsTypeless) {
  MailboxObject typed_mb(5);
  MailboxObject untyped_mb(5);

  typed_mb.TryPut(Msg(100).Get());
  untyped_mb.TryPut(Msg(100).Get());

  Logic4Snapshot t_msg;
  Logic4Snapshot u_msg;
  typed_mb.TryGet(t_msg);
  untyped_mb.TryGet(u_msg);
  EXPECT_EQ(Word(t_msg), Word(u_msg));
}

// §15.4.9 (printed page 377): a parameterized mailbox provides the same
// methods as the typeless one, so `mailbox #(int)` takes a put() and hands
// the message to get(): 3 and a num() of 0 read as 30. Left unlowered, the
// parameterized declaration created no queue and r read x.
TEST(MailboxSim, ParameterizedMailboxCarriesItsMessages) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox #(int) mb = new;\n"
      "  int a, r;\n"
      "  initial begin\n"
      "    mb.put(3);\n"
      "    mb.get(a);\n"
      "    r = a * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

}  // namespace
