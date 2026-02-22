// §15.3.4: Try_get()

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
// 3. Semaphore: try_get() non-blocking (section 15.3.3)
// =============================================================================
TEST(IpcSync, SemaphoreTryGetSucceeds) {
  SemaphoreObject sem(3);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetFails) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet(2);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(sem.key_count, 1);  // Keys unchanged on failure.
}

TEST(IpcSync, SemaphoreTryGetDefaultOne) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet();
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreTryGetExactKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);  // Empty now.
}

// =============================================================================
// 17. Semaphore: TryGet with count=0 always succeeds
// =============================================================================
TEST(IpcSync, SemaphoreTryGetZeroCount) {
  SemaphoreObject sem(0);
  // Requesting 0 keys should always succeed (0 >= 0).
  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

}  // namespace
