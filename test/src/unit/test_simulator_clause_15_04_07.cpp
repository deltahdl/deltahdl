// §15.4.7: Peek()

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
// 9. Mailbox: try_peek() (section 15.4.5)
// =============================================================================
TEST(IpcSync, MailboxTryPeekSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);  // Peek does not remove.
}

TEST(IpcSync, MailboxTryPeekEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryPeek(msg), -1);
}

// =============================================================================
// 18. Mailbox: Peek does not consume
// =============================================================================
TEST(IpcSync, MailboxPeekDoesNotConsume) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  // Multiple peeks should return same value.
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  mb.TryPeek(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 1);
  // Get consumes it.
  mb.TryGet(msg);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

}  // namespace
