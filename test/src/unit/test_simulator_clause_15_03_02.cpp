#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

TEST(IpcSync, SemaphorePutAddsKeys) {
  SemaphoreObject sem(0);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutDefaultAddsOne) {
  SemaphoreObject sem(0);
  EXPECT_TRUE(sem.Put());
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphorePutWakesWaiters) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphorePutNegativeCountReturnsError) {
  SemaphoreObject sem(5);
  EXPECT_FALSE(sem.Put(-1));
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutNegativeCountUnchanged) {
  SemaphoreObject sem(3);
  sem.Put(-10);
  EXPECT_EQ(sem.key_count, 3);
}

TEST(IpcSync, SemaphorePutZeroCountNoChange) {
  SemaphoreObject sem(5);
  EXPECT_TRUE(sem.Put(0));
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutReturnsTrue) {
  SemaphoreObject sem(0);
  EXPECT_TRUE(sem.Put(1));
  EXPECT_TRUE(sem.Put(10));
}

TEST(IpcSync, SemaphorePutOnNegativeKeyCount) {
  SemaphoreObject sem(-5);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, -2);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
}

}
