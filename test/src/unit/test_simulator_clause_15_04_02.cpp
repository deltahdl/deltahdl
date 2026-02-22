// §15.4.2: Num()

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
// 21. Mailbox: Num reflects current state
// =============================================================================
TEST(IpcSync, MailboxNumReflectsState) {
  MailboxObject mb;
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

}  // namespace
