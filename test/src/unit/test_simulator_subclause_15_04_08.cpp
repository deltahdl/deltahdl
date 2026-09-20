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

// Two non-equivalent message types, §6.22.2 c)'s int and §6.22.1 a)'s string.
constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

// §15.4.8: a message is available but its type is not equivalent to the
// variable type, so try_peek() returns a negative integer and copies nothing.
TEST(IpcSync, MailboxTryPeekTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xBEEF);
  EXPECT_LT(mb.TryPeek(msg, kTypeString), 0);
  EXPECT_EQ(Word(msg), 0xBEEFu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.8: an available, type-equivalent message is copied out (not removed)
// and a positive integer is returned.
TEST(IpcSync, MailboxTryPeekMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_GT(mb.TryPeek(msg, kTypeInt), 0);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.8: the empty 0 and the type-mismatch negative are distinct outcomes.
TEST(IpcSync, MailboxTryPeekEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryPeek(msg, kTypeString), 0);
}

// §15.4.8 (printed pages 376-377): try_peek() copies the front message
// without removing it and returns a positive integer, so the status 1, the
// copied 4 and a num() still of 1 read as 141; on an empty mailbox it
// returns 0 and copies nothing, leaving x at 5: 50. Left unlowered, the calls
// evaluated to nothing and both read x.
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

// §15.4.8 (printed page 377): when the type of the message variable is not
// equivalent to the type of the message in the mailbox, try_peek() returns a
// negative integer and copies nothing. The typeless mailbox holds a 16-bit
// vector, and try_peek() into a 32-bit int -- §6.22.2 c) has two integral
// types equivalent only at one total width -- answers -1 and leaves x at
// 5: -1 and 5. An untyped copy answered 1 and stored the vector's value.
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

}  // namespace
