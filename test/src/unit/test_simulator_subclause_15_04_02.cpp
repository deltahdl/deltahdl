#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, MailboxNumReflectsState) {
  delta::MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  mb.TryPut(1);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryPut(2);
  EXPECT_EQ(mb.Num(), 2);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 1);
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxNumAtBound) {
  delta::MailboxObject mb(3);
  mb.TryPut(1);
  mb.TryPut(2);
  mb.TryPut(3);
  EXPECT_EQ(mb.Num(), 3);
  EXPECT_EQ(mb.TryPut(4), 0);
  EXPECT_EQ(mb.Num(), 3);
}

// num() reports the live message count. A retrieval attempt on an empty
// mailbox removes nothing, so num() must keep reporting zero rather than
// underflowing — the read-side mirror of the at-bound put case above.
TEST(IpcSync, MailboxNumUnchangedByFailedGet) {
  delta::MailboxObject mb;
  EXPECT_EQ(mb.Num(), 0);
  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(mb.Num(), 0);
}

}  // namespace
