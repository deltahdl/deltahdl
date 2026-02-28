// §15.4.5: Get()

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace {

// =============================================================================
// 7. Mailbox: try_put() / num() (section 15.4.3)
// =============================================================================
TEST(IpcSync, MailboxTryPutUnbounded) {
  MailboxObject mb;
  EXPECT_EQ(mb.TryPut(42), 0);
  EXPECT_EQ(mb.TryPut(99), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedSuccess) {
  MailboxObject mb(2);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), 0);
  EXPECT_EQ(mb.Num(), 2);
}

TEST(IpcSync, MailboxTryPutBoundedFull) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);  // Full.
  EXPECT_EQ(mb.Num(), 1);
}

// =============================================================================
// 11. Mailbox: Bounded put then get frees space
// =============================================================================
TEST(IpcSync, MailboxBoundedGetFreesSpace) {
  MailboxObject mb(1);
  EXPECT_EQ(mb.TryPut(10), 0);
  EXPECT_EQ(mb.TryPut(20), -1);  // Full.

  uint64_t msg = 0;
  mb.TryGet(msg);
  EXPECT_EQ(msg, 10u);
  EXPECT_EQ(mb.TryPut(30), 0);  // Space freed.
  EXPECT_EQ(mb.Num(), 1);
}

}  // namespace
