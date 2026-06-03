#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxPutUnboundedAlwaysPlaced) {
  MailboxObject mb;
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(20), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 3);
}

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

TEST(IpcSync, MailboxPutBoundedBlocksWhenFull) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(1), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(2), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(3), MbxPutStatus::kBlock);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxPutSucceedsAfterGet) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.Put(42), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(99), MbxPutStatus::kBlock);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Put(99), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.3: a put() blocked on a full bounded mailbox stores nothing while it
// waits, and once room frees the message joins the queue in strict FIFO order
// — at the tail, behind a message that is already enqueued. With a second
// message still present when the slot opens, draining must yield the older
// message first and the once-blocked message last.
TEST(IpcSync, MailboxPutAfterBlockAppendsAtTail) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.Put(10), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(20), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kBlock);  // full: not stored
  EXPECT_EQ(mb.Num(), 2);

  uint64_t msg = 0;
  mb.TryGet(msg);                               // frees a slot, removes 10
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.Put(30), MbxPutStatus::kPlaced);  // now stored, at the tail
  EXPECT_EQ(mb.Num(), 2);

  mb.TryGet(msg);
  EXPECT_EQ(msg, 20u);  // the message queued ahead exits first
  mb.TryGet(msg);
  EXPECT_EQ(msg, 30u);  // the once-blocked message exits last
}

}
