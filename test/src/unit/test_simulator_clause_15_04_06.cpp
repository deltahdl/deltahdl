// §15.4.6: Try_get()

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"
#include "fixture_simulator.h"

namespace {

// =============================================================================
// 8. Mailbox: try_get() (section 15.4.4)
// =============================================================================
TEST(IpcSync, MailboxTryGetSuccess) {
  MailboxObject mb;
  mb.TryPut(42);
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), 0);
  EXPECT_EQ(msg, 42u);
  EXPECT_EQ(mb.Num(), 0);
}

TEST(IpcSync, MailboxTryGetEmpty) {
  MailboxObject mb;
  uint64_t msg = 0;
  EXPECT_EQ(mb.TryGet(msg), -1);
}

}  // namespace
