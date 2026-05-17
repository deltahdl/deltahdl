#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxPeekCopiesWithoutRemoving) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

TEST(IpcSync, MailboxPeekEmptyReturnsBlock) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kBlock);
}

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

}
