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

TEST(IpcSync, SemaphoreLargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, MultipleSemaphoresInContext) {
  SyncFixture f;
  auto* sem1 = f.ctx.CreateSemaphore("s1", 1);
  auto* sem2 = f.ctx.CreateSemaphore("s2", 5);
  EXPECT_EQ(sem1->key_count, 1);
  EXPECT_EQ(sem2->key_count, 5);
  EXPECT_NE(f.ctx.FindSemaphore("s1"), f.ctx.FindSemaphore("s2"));
}

// §15.3: Semaphore as mutual exclusion — one key means only one
// process can hold it at a time; others fail TryGet until Put.
TEST(IpcSync, SemaphoreMutualExclusionPattern) {
  SemaphoreObject sem(1);
  // First process acquires the key.
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
  // Second process cannot acquire — bucket empty.
  EXPECT_EQ(sem.TryGet(1), 0);
  EXPECT_EQ(sem.key_count, 0);
  // First process returns the key.
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
  // Now the second process can acquire.
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: Key count can increase beyond initial allocation via Put.
TEST(IpcSync, SemaphoreKeyCountCanExceedInitial) {
  SemaphoreObject sem(2);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
}

}  // namespace
