#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxTryPeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;

  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);

  mb.TryGet(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryPeekDoesNotModifyMsgOnEmpty) {
  MailboxObject mb;
  uint64_t msg = 0xBEEF;
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 0xBEEFu);
}

TEST(IpcSync, MailboxTryPeekReturnsFront) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Num(), 2);
}

// Arbitrary, distinct type ids standing in for two non-equivalent data types.
constexpr uint32_t kTypeInt = 1;
constexpr uint32_t kTypeString = 2;

// §15.4.8: a message is available but its type is not equivalent to the
// variable type, so try_peek() returns a negative integer and copies nothing.
TEST(IpcSync, MailboxTryPeekTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0xBEEF;
  EXPECT_LT(mb.TryPeek(msg, kTypeString), 0);
  EXPECT_EQ(msg, 0xBEEFu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.8: an available, type-equivalent message is copied out (not removed)
// and a positive integer is returned.
TEST(IpcSync, MailboxTryPeekMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_GT(mb.TryPeek(msg, kTypeInt), 0);
  EXPECT_EQ(msg, 0xABu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.8: the empty 0 and the type-mismatch negative are distinct outcomes.
TEST(IpcSync, MailboxTryPeekEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  uint64_t msg = 0;
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

}  // namespace
