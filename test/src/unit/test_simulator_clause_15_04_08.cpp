#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.8: try_peek on non-empty mailbox returns positive int and copies message.
TEST(IpcSync, MailboxTryPeekSuccessReturnsPositive) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
}

// §15.4.8: try_peek on empty mailbox returns 0.
TEST(IpcSync, MailboxTryPeekEmptyReturnsZero) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 0);
}

// §15.4.8: try_peek does not consume the message.
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

// §15.4.8: try_peek does not modify msg when mailbox is empty.
TEST(IpcSync, MailboxTryPeekDoesNotModifyMsgOnEmpty) {
  MailboxObject mb;
  uint64_t msg = 0xBEEF;
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 0xBEEFu);
}

// §15.4.8: try_peek always returns the front message (FIFO).
TEST(IpcSync, MailboxTryPeekReturnsFront) {
  MailboxObject mb;
  mb.TryPut(100);
  mb.TryPut(200);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(msg, 100u);
  EXPECT_EQ(mb.Num(), 2);
}

}  // namespace
