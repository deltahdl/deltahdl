#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

TEST(IpcSync, SemaphoreNewDefaultKeys) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewWithKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphoreNewNegativeInitialKeys) {
  SemaphoreObject sem(-3);
  EXPECT_EQ(sem.key_count, -3);
}

TEST(IpcSync, SemaphoreNewNegativeTryGetFailsUntilPositive) {
  SemaphoreObject sem(-2);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewNegativeGetBlocksUntilPositive) {
  // The procure guard also governs the blocking get() path: a semaphore made
  // with a negative initial key count must block get() requests until enough
  // keys have been returned to satisfy the requested amount.
  SemaphoreObject sem(-1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
  sem.Put(1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewReturnsHandle) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("s", 4);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 4);
}

}
