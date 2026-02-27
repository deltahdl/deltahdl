// §15.3.1: New()

#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/sync_objects.h"
#include "fixture_simulator.h"

namespace {

// =============================================================================
// 1. Semaphore: Constructor with key count (section 15.3)
// =============================================================================
TEST(IpcSync, SemaphoreNewDefaultKeys) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewWithKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

}  // namespace
