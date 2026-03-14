#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.5: Get retrieves and removes the front message.
TEST(IpcSync, MailboxGetRetrievesFrontMessage) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.5: Get on empty mailbox returns kBlock.
TEST(IpcSync, MailboxGetEmptyReturnsBlock) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.5: Get retrieves in FIFO order.
TEST(IpcSync, MailboxGetFifoOrder) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  mb.TryPut(300);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 200u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 300u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
}

// §15.4.5: Get frees space in a bounded mailbox for subsequent put.
TEST(IpcSync, MailboxGetFreesSpaceForPut) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.5: Consecutive get calls drain the mailbox.
TEST(IpcSync, MailboxGetDrainsMailbox) {
  MailboxObject mb;
  for (uint64_t i = 0; i < 50; ++i) {
    mb.TryPut(i);
  }
  EXPECT_EQ(mb.Num(), 50);
  for (uint64_t i = 0; i < 50; ++i) {
    uint64_t msg = 0;
    EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
    EXPECT_EQ(msg, i);
  }
  EXPECT_EQ(mb.Num(), 0);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kBlock);
}

}  // namespace
