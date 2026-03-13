#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

// §15.3.2: put() adds the specified number of keys.
TEST(IpcSync, SemaphorePutAddsKeys) {
  SemaphoreObject sem(0);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 5);
}

// §15.3.2: put() default keyCount is 1.
TEST(IpcSync, SemaphorePutDefaultAddsOne) {
  SemaphoreObject sem(0);
  EXPECT_TRUE(sem.Put());
  EXPECT_EQ(sem.key_count, 1);
}

// §15.3.2: put() wakes waiters when enough keys are returned.
TEST(IpcSync, SemaphorePutWakesWaiters) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
}

// §15.3.2: Negative keyCount results in an error (returns false).
TEST(IpcSync, SemaphorePutNegativeCountReturnsError) {
  SemaphoreObject sem(5);
  EXPECT_FALSE(sem.Put(-1));
  EXPECT_EQ(sem.key_count, 5);
}

// §15.3.2: Negative keyCount does not modify key_count.
TEST(IpcSync, SemaphorePutNegativeCountUnchanged) {
  SemaphoreObject sem(3);
  sem.Put(-10);
  EXPECT_EQ(sem.key_count, 3);
}

// §15.3.2: put(0) is valid and does not change key count.
TEST(IpcSync, SemaphorePutZeroCountNoChange) {
  SemaphoreObject sem(5);
  EXPECT_TRUE(sem.Put(0));
  EXPECT_EQ(sem.key_count, 5);
}

// §15.3.2: put() returns true on success.
TEST(IpcSync, SemaphorePutReturnsTrue) {
  SemaphoreObject sem(0);
  EXPECT_TRUE(sem.Put(1));
  EXPECT_TRUE(sem.Put(10));
}

// §15.3.2: put() on semaphore with negative key count brings it positive.
TEST(IpcSync, SemaphorePutOnNegativeKeyCount) {
  SemaphoreObject sem(-5);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, -2);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
}

}  // namespace
