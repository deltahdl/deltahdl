#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.7: Peek copies front message without removing it.
TEST(IpcSync, MailboxPeekCopiesWithoutRemoving) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.7: Peek on empty mailbox returns kBlock.
TEST(IpcSync, MailboxPeekEmptyReturnsBlock) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kBlock);
}

// §15.4.7: Multiple peeks return the same front message.
TEST(IpcSync, MailboxPeekRepeatedReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Num(), 2);
}

// §15.4.7: Peek followed by Get retrieves the same message.
TEST(IpcSync, MailboxPeekThenGetReturnsSameMessage) {
  MailboxObject mb;
  mb.TryPut(55);
  uint64_t peek_msg = 0;
  uint64_t get_msg = 0;
  EXPECT_EQ(mb.Peek(peek_msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(mb.Get(get_msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(peek_msg, get_msg);
  EXPECT_EQ(mb.Num(), 0);
}

// §15.4.7: Peek after get returns the next message.
TEST(IpcSync, MailboxPeekAfterGetReturnsNext) {
  MailboxObject mb;
  mb.TryPut(10);
  mb.TryPut(20);
  uint64_t msg = 0;
  mb.Get(msg);
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 20u);
  EXPECT_EQ(mb.Num(), 1);
}

}  // namespace
