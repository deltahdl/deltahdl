// §15.5.1: Triggering an event

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
// 22. Event variable creation with is_event flag
// =============================================================================
TEST(IpcSync, EventVariableCreation) {
  SyncFixture f;
  auto* ev = f.ctx.CreateVariable("ev1", 1);
  ev->is_event = true;
  ev->value = MakeLogic4VecVal(f.arena, 1, 0);

  auto* found = f.ctx.FindVariable("ev1");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_event);
}

}  // namespace
