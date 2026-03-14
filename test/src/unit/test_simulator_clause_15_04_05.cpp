#include <gtest/gtest.h>

#include <cstdint>

#include "simulator/sync_objects.h"

using namespace delta;

namespace {

// §15.4.5: get retrieves and removes from front (FIFO).
TEST(IpcSync, MailboxGetFreesSpaceForPut) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 1);
  EXPECT_EQ(mb.TryPut(20), 0);

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 1);
  EXPECT_EQ(mb.Num(), 1);
}

}  // namespace
