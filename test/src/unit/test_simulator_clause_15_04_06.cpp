#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxTryGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  mb.TryPut(30);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 20u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 30u);
  EXPECT_EQ(mb.TryGet(msg), 0);
}

TEST(IpcSync, MailboxTryGetDoesNotModifyMsgOnFailure) {
  MailboxObject mb;
  uint64_t msg = 0xDEAD;
  EXPECT_EQ(mb.TryGet(msg), 0);
  EXPECT_EQ(msg, 0xDEADu);
}

TEST(IpcSync, MailboxTryGetFreesSpaceBounded) {
  MailboxObject mb(1);
  mb.TryPut(10);
  EXPECT_EQ(mb.TryPut(20), 0);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

// Arbitrary, distinct type ids standing in for two non-equivalent data types.
constexpr uint32_t kTypeInt = 1;
constexpr uint32_t kTypeString = 2;

// §15.4.6: a message is available but its type is not equivalent to the
// variable type, so try_get() returns a negative integer (distinct from the 0
// returned for an empty mailbox) and leaves the message in the queue.
TEST(IpcSync, MailboxTryGetTypeMismatchReturnsNegative) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0xDEAD;
  EXPECT_LT(mb.TryGet(msg, kTypeString), 0);
  EXPECT_EQ(msg, 0xDEADu);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.6: a message is available and its type is equivalent, so the message is
// retrieved and a positive integer is returned.
TEST(IpcSync, MailboxTryGetMatchingTypeReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(0xAB, kTypeInt);
  uint64_t msg = 0;
  EXPECT_GT(mb.TryGet(msg, kTypeInt), 0);
  EXPECT_EQ(msg, 0xABu);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.6: the empty-mailbox 0 and the type-mismatch negative are distinct
// outcomes — an empty mailbox never reports a type error.
TEST(IpcSync, MailboxTryGetEmptyDistinctFromTypeMismatch) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg, kTypeString), 0);
}

}  // namespace
