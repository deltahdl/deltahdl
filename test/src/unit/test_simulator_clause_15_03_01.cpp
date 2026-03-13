#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

// §15.3.1: Default keyCount is 0.
TEST(IpcSync, SemaphoreNewDefaultKeys) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3.1: Explicit keyCount sets initial keys.
TEST(IpcSync, SemaphoreNewWithKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

// §15.3.1: Initial value may be negative.
TEST(IpcSync, SemaphoreNewNegativeInitialKeys) {
  SemaphoreObject sem(-3);
  EXPECT_EQ(sem.key_count, -3);
}

// §15.3.1: Keys must be positive before get()/try_get() can procure.
// With negative initial keys, TryGet fails until Put brings count positive.
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

// §15.3.1: new() with zero keyCount — TryGet fails immediately.
TEST(IpcSync, SemaphoreNewZeroKeysTryGetFails) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(1), 0);
}

// §15.3.1: new() returns the semaphore handle (via CreateSemaphore).
TEST(IpcSync, SemaphoreNewReturnsHandle) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("s", 4);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 4);
}

// §15.3.1: new(1) — single key semaphore (binary mutex).
TEST(IpcSync, SemaphoreNewSingleKey) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
}

}  // namespace
