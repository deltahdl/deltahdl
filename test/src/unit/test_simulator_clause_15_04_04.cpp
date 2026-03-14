#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.4: try_put on unbounded mailbox always returns positive.
TEST(IpcSync, MailboxTryPutUnboundedSucceeds) {
  MailboxObject mb;
  EXPECT_EQ(mb.TryPut(42), 1);
  EXPECT_EQ(mb.TryPut(99), 1);
  EXPECT_EQ(mb.Num(), 2);
}

// §15.4.4: try_put on bounded mailbox with room returns positive.
TEST(IpcSync, MailboxTryPutBoundedWithRoom) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 1);
  EXPECT_EQ(mb.Num(), 2);
}

// §15.4.4: try_put on bounded mailbox when full returns 0.
TEST(IpcSync, MailboxTryPutBoundedFullReturnsZero) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.4: try_put stores messages in FIFO order.
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

// §15.4.4: Unbounded mailboxes are never full — try_put always succeeds.
TEST(IpcSync, MailboxTryPutUnboundedNeverFull) {
  MailboxObject mb;
  for (int i = 0; i < 100; ++i) {
    EXPECT_EQ(mb.TryPut(static_cast<uint64_t>(i)), 1);
  }
  EXPECT_EQ(mb.Num(), 100);
}

// §15.4.4: try_put succeeds after space freed by get on bounded mailbox.
TEST(IpcSync, MailboxTryPutSucceedsAfterGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

}  // namespace
