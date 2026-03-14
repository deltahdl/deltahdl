#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.3: Put on unbounded mailbox always succeeds.
TEST(IpcSync, MailboxPutUnboundedAlwaysPlaced) {
  MailboxObject mb;
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(20), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 3);
}

// §15.4.3: Put stores messages in FIFO order.
TEST(IpcSync, MailboxPutFifoOrder) {
  MailboxObject mb;
  mb.Put(100);
  mb.Put(200);
  mb.Put(300);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 100u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 200u);
  mb.TryGet(msg);
  EXPECT_EQ(msg, 300u);
}

// §15.4.3: Put on bounded mailbox returns kBlock when full.
TEST(IpcSync, MailboxPutBoundedBlocksWhenFull) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(1), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(2), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(3), MbxPutStatus::kBlock);
  EXPECT_EQ(mb.Num(), 2);
}

// §15.4.3: Put succeeds after space is freed by get.
TEST(IpcSync, MailboxPutSucceedsAfterGet) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(42), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(99), MbxPutStatus::kBlock);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Put(99), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.3: Many puts on unbounded mailbox all succeed.
TEST(IpcSync, MailboxPutUnboundedManyMessages) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 100; ++i) {
    EXPECT_EQ(mb.Put(i), MbxPutStatus::kPlaced);
  }
  EXPECT_EQ(mb.Num(), 100);
}

}  // namespace
