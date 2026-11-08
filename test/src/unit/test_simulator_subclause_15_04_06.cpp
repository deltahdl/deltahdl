#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_string_var.h"
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

constexpr MailboxMessageType kTypeInt =
    MailboxMessageType::Integral(32, true, MailboxMessageType::States::kTwo);
constexpr MailboxMessageType kTypeString = MailboxMessageType::String();

TEST(IpcSync, MailboxTryGetTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg = Msg(0xDEAD);
  EXPECT_LT(mb.TryGet(msg, kTypeString), 0);
  EXPECT_EQ(Word(msg), 0xDEADu);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxTryGetMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(Msg(0xAB).Get(), kTypeInt);
  Logic4Snapshot msg;
  EXPECT_GT(mb.TryGet(msg, kTypeInt), 0);
  EXPECT_EQ(Word(msg), 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryGetEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  Logic4Snapshot msg;
  EXPECT_EQ(mb.TryGet(msg, kTypeString), 0);
}

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
