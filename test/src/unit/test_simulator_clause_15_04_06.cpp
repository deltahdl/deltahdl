#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxTryGetSuccessReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryGetEmptyReturnsZero) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 0);
}

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

}
