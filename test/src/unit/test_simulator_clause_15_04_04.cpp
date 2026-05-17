#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxTryPutUnboundedSucceeds) {
  MailboxObject mb;
  EXPECT_EQ(mb.TryPut(42), 1);
  EXPECT_EQ(mb.TryPut(99), 1);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedWithRoom) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 1);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedFullReturnsZero) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxTryPutFifoOrder) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  mb.TryPut(300);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 100u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 200u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 300u);
}

TEST(IpcSync, MailboxTryPutUnboundedNeverFull) {
  MailboxObject mb;
  for (int i = 0; i < 100; ++i) {
    EXPECT_EQ(mb.TryPut(static_cast<uint64_t>(i)), 1);
  }
  EXPECT_EQ(mb.Num(), 100);
}

TEST(IpcSync, MailboxTryPutSucceedsAfterGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

}
