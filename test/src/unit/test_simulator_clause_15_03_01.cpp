// §15.3.1: New()

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
