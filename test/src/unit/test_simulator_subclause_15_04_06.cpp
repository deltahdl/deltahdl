#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_string_var.h"
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

TEST(IpcSync, MailboxTryGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(Msg(10).Get());
  mb.TryPut(Msg(20).Get());
  mb.TryPut(Msg(30).Get());
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(Word(msg), 10u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(Word(msg), 20u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(Word(msg), 30u);
  EXPECT_EQ(mb.TryGet(msg), 0);
}

TEST(IpcSync, MailboxTryGetDoesNotModifyMsgOnFailure) {
  MailboxObject mb;
  Logic4Snapshot msg = Msg(0xDEAD);
  EXPECT_EQ(mb.TryGet(msg), 0);
  EXPECT_EQ(Word(msg), 0xDEADu);
}

TEST(IpcSync, MailboxTryGetFreesSpaceBounded) {
  MailboxObject mb(1);
  mb.TryPut(Msg(10).Get());
  EXPECT_EQ(mb.TryPut(Msg(20).Get()), 0);
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(mb.TryPut(Msg(30).Get()), 1);
  EXPECT_EQ(mb.Num(), 1);
}

// Two non-equivalent message types, §6.22.2 c)'s int and §6.22.1 a)'s string.
constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

// §15.4.6: a message is available but its type is not equivalent to the
// variable type, so try_get() returns a negative integer (distinct from the 0
// returned for an empty mailbox) and leaves the message in the queue.
TEST(IpcSync, MailboxTryGetTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xDEAD);
  EXPECT_LT(mb.TryGet(msg, kTypeString), 0);
  EXPECT_EQ(Word(msg), 0xDEADu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.6: a message is available and its type is equivalent, so the message is
// retrieved and a positive integer is returned.
TEST(IpcSync, MailboxTryGetMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_GT(mb.TryGet(msg, kTypeInt), 0);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.6: the empty-mailbox 0 and the type-mismatch negative are distinct
// outcomes — an empty mailbox never reports a type error.
TEST(IpcSync, MailboxTryGetEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryGet(msg, kTypeString), 0);
}

// §15.4.6 (printed page 376): try_get() on an empty mailbox returns 0 without
// waiting, and retrieves nothing, so the variable it names keeps the 5 it
// held; a try_get() that finds a message retrieves it and returns a positive
// integer. 0 and 5 read as 105, then 1 and 9 as 119. Left unlowered, the
// calls evaluated to nothing and r read x.
TEST(MailboxSim, TryGetOnEmptyLeavesTheVariableAndAnswersZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, status, r;\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    status = mb.try_get(x);\n"
      "    r = 100 + status * 10 + x;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 105u);
}

TEST(MailboxSim, TryGetRetrievesAnAvailableMessage) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  int x, status, r;\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    mb.put(9);\n"
      "    status = mb.try_get(x);\n"
      "    r = 100 + status * 10 + x;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 119u);
}

// §15.4.6 (printed page 376): when the type of the message variable is not
// equivalent to the type of the message in the mailbox, try_get() returns a
// negative integer, and the message stays where it is. The typeless mailbox
// holds the int 7, so try_get() into a string answers -1, leaves the string
// holding "keep" and num() still counts 1. An untyped retrieval answered 1,
// stored the 7 over the string and counted 0.
TEST(MailboxSim, TryGetIntoAVariableOfAnotherTypeAnswersNegative) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  string s = \"keep\";\n"
      "  int status, n;\n"
      "  initial begin\n"
      "    mb.put(7);\n"
      "    status = mb.try_get(s);\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "status");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "keep");
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 1u);
}

// §15.4.6 (printed page 376): a message whose type is equivalent to the
// variable's is retrieved and try_get() returns a positive integer. The
// typeless mailbox holds a string literal, and the string variable takes it
// whole: 1, "swap" and a num() of 0. Held as a 64-bit word, the retrieval
// still answered 1 but sized the characters to the variable's, and a string
// of five characters or more read back cut to those the variable had.
TEST(MailboxSim, TryGetOfAnEquivalentTypeRetrievesTheMessage) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  mailbox mb = new;\n"
      "  string s = \"keep\";\n"
      "  int status, n;\n"
      "  initial begin\n"
      "    mb.put(\"swapped\");\n"
      "    status = mb.try_get(s);\n"
      "    n = mb.num();\n"
      "  end\n"
      "endmodule\n",
      f, "status");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "swapped");
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 0u);
}

}  // namespace
