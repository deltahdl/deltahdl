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

TEST(IpcSync, MailboxTryPeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(Msg(42).Get());
  Logic4Snapshot msg;

  mb.TryPeek(msg);
  EXPECT_EQ(Word(msg), 42u);
  mb.TryPeek(msg);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.Num(), 1);

  mb.TryGet(msg);
  EXPECT_EQ(Word(msg), 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryPeekDoesNotModifyMsgOnEmpty) {
  MailboxObject mb;
  Logic4Snapshot msg = Msg(0xBEEF);
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(Word(msg), 0xBEEFu);
}

TEST(IpcSync, MailboxTryPeekReturnsFront) {
  MailboxObject mb;
  mb.TryPut(Msg(100).Get());
  mb.TryPut(Msg(200).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(Word(msg), 100u);
  EXPECT_EQ(mb.Num(), 2);
}

constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

TEST(IpcSync, MailboxTryPeekTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xBEEF);
  EXPECT_LT(mb.TryPeek(msg, kTypeString), 0);
  EXPECT_EQ(Word(msg), 0xBEEFu);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxTryPeekMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_GT(mb.TryPeek(msg, kTypeInt), 0);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxTryPeekEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryPeek(msg, kTypeString), 0);
}

TEST(MailboxSim, TryPeekCopiesWithoutRemoving) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, status, r;\n"
      "  initial begin\n"
      "    mb.put(4);\n"
      "    status = mb.try_peek(x);\n"
      "    r = status * 100 + x * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 141u);
}

TEST(MailboxSim, TryPeekOnEmptyLeavesTheVariableAndAnswersZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, status, r;\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    status = mb.try_peek(x);\n"
      "    r = x * 10 + status;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(MailboxSim, TryPeekIntoAVariableOfAnotherTypeAnswersNegative) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  bit [15:0] h = 16'h1234;\n"
      "  int x, status;\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    mb.put(h);\n"
      "    status = mb.try_peek(x);\n"
      "  end\n"
      "endmodule\n",
      f, "status");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
}

TEST(MailboxSim, TryPeekOfAComputedMessageChecksItsWidthAndSign) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  bit [15:0] a = 16'd40;\n"
      "  bit [31:0] u;\n"
      "  int x, sx, su, r;\n"
      "  initial begin\n"
      "    mb.put(a + 2);\n"
      "    sx = mb.try_peek(x);\n"
      "    su = mb.try_peek(u);\n"
      "    r = (sx == -1) * 1000 + su * 100 + u;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1142u);
}

TEST(MailboxSim, TryPeekIntoAnElementOfAnotherTypeAnswersNegative) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  bit [15:0] h = 16'h1234;\n"
      "  int arr[2];\n"
      "  int i = 1, status, r;\n"
      "  initial begin\n"
      "    arr[1] = 5;\n"
      "    mb.put(h);\n"
      "    status = mb.try_peek(arr[i]);\n"
      "    r = (status == -1) * 100 + arr[1] * 10 + mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 151u);
}

}  // namespace
