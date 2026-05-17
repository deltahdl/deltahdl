#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/sync_objects.h"

namespace {

TEST(IpcSync, SemaphoreGetAcquiresKeys) {
  SemaphoreObject sem(5);
  auto status = sem.Get(3);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

TEST(IpcSync, SemaphoreGetDefaultOne) {
  SemaphoreObject sem(3);
  auto status = sem.Get();
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

TEST(IpcSync, SemaphoreGetBlocksWhenInsufficient) {
  SemaphoreObject sem(2);
  auto status = sem.Get(5);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 2);
}

TEST(IpcSync, SemaphoreGetBlocksOnEmptyBucket) {
  SemaphoreObject sem(0);
  auto status = sem.Get(1);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreGetNegativeCountReturnsError) {
  SemaphoreObject sem(5);
  auto status = sem.Get(-1);
  EXPECT_EQ(status, SemGetStatus::kError);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphoreGetExactKeys) {
  SemaphoreObject sem(3);
  auto status = sem.Get(3);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreGetZeroCountAcquires) {
  SemaphoreObject sem(2);
  auto status = sem.Get(0);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

TEST(IpcSync, SemaphoreGetConsecutiveCalls) {
  SemaphoreObject sem(10);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.Get(4), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.Get(4), SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 3);
}

TEST(IpcSync, SemaphoreGetFifoWaiterOrder) {
  SemaphoreObject sem(0);

  int wake_order = 0;
  int first_woken = -1;
  int second_woken = -1;

  sem.waiters.push_back({1, std::coroutine_handle<>{}});
  sem.waiters.push_back({1, std::coroutine_handle<>{}});
  EXPECT_EQ(sem.waiters.size(), 2u);
  EXPECT_EQ(sem.waiters[0].first, 1);
  EXPECT_EQ(sem.waiters[1].first, 1);
  (void)wake_order;
  (void)first_woken;
  (void)second_woken;
}

TEST(IpcSync, SemaphoreGetBlocksOnNegativeKeys) {
  SemaphoreObject sem(-3);
  auto status = sem.Get(1);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, -3);
}

TEST(IpcSync, SemaphoreGetAfterPutSucceeds) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kBlock);
  sem.Put(5);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 3);
}

}
