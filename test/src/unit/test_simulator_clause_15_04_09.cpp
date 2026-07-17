#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxParameterizedSameMethodsAsDynamic) {
  MailboxObject mb;

  EXPECT_EQ(mb.Num(), 0);
  EXPECT_EQ(mb.Put(42), MbxPutStatus::kPlaced);
  EXPECT_EQ(mb.TryPut(43), 1);
  EXPECT_EQ(mb.Num(), 2);

  uint64_t msg = 0;
  EXPECT_EQ(mb.Peek(msg), MbxPeekStatus::kCopied);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.TryPeek(msg), 1);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Get(msg), MbxGetStatus::kRetrieved);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.TryGet(msg), 1);
  EXPECT_EQ(msg, 43u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxParameterizedSameRuntimeAsTypeless) {
  MailboxObject typed_mb(5);
  MailboxObject untyped_mb(5);

  typed_mb.TryPut(100);
  untyped_mb.TryPut(100);

  uint64_t t_msg = 0;
  uint64_t u_msg = 0;
  typed_mb.TryGet(t_msg);
  untyped_mb.TryGet(u_msg);
  EXPECT_EQ(t_msg, u_msg);
}

}  // namespace
