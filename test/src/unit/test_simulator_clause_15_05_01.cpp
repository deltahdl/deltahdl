// §15.5.1: Triggering an event

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
