#include <gtest/gtest.h>

#include <cstdint>

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

}  // namespace
