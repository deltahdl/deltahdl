// §15.3: Semaphores

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
// 4. Semaphore: Context registration (section 15.3)
// =============================================================================
TEST(IpcSync, SemaphoreContextCreateFind) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("sem1", 3);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 3);

  auto* found = f.ctx.FindSemaphore("sem1");
  EXPECT_EQ(found, sem);

  auto* not_found = f.ctx.FindSemaphore("no_such_sem");
  EXPECT_EQ(not_found, nullptr);
}

// =============================================================================
// 14. Semaphore: Multiple put/tryget cycles
// =============================================================================
TEST(IpcSync, SemaphoreMultiplePutTryGetCycles_DrainKeys) {
  SemaphoreObject sem(0);
  sem.Put(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(7), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreMultiplePutTryGetCycles_RefillAndDrain) {
  SemaphoreObject sem(0);
  sem.Put(10);
  sem.TryGet(10);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// =============================================================================
// 20. Semaphore: Large key count
// =============================================================================
TEST(IpcSync, SemaphoreLargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// =============================================================================
// 23. Multiple semaphores in same context
// =============================================================================
TEST(IpcSync, MultipleSemaphoresInContext) {
  SyncFixture f;
  auto* sem1 = f.ctx.CreateSemaphore("s1", 1);
  auto* sem2 = f.ctx.CreateSemaphore("s2", 5);
  EXPECT_EQ(sem1->key_count, 1);
  EXPECT_EQ(sem2->key_count, 5);
  EXPECT_NE(f.ctx.FindSemaphore("s1"), f.ctx.FindSemaphore("s2"));
}

}  // namespace
