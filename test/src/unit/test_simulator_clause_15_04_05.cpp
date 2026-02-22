// §15.4.5: Get()

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/sync_objects.h"
#include "simulation/variable.h"

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
struct SyncFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, 42};
};

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
