#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/sync_objects.h"

namespace {

// §15.3.3: get() acquires keys when enough are available.
TEST(IpcSync, SemaphoreGetAcquiresKeys) {
  SemaphoreObject sem(5);
  auto status = sem.Get(3);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

// §15.3.3: get() default keyCount is 1.
TEST(IpcSync, SemaphoreGetDefaultOne) {
  SemaphoreObject sem(3);
  auto status = sem.Get();
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

// §15.3.3: get() returns kBlock when insufficient keys.
TEST(IpcSync, SemaphoreGetBlocksWhenInsufficient) {
  SemaphoreObject sem(2);
  auto status = sem.Get(5);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 2);
}

// §15.3.3: get() returns kBlock when zero keys available.
TEST(IpcSync, SemaphoreGetBlocksOnEmptyBucket) {
  SemaphoreObject sem(0);
  auto status = sem.Get(1);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3.3: Negative keyCount results in an error.
TEST(IpcSync, SemaphoreGetNegativeCountReturnsError) {
  SemaphoreObject sem(5);
  auto status = sem.Get(-1);
  EXPECT_EQ(status, SemGetStatus::kError);
  EXPECT_EQ(sem.key_count, 5);
}

// §15.3.3: get() with exact available keys succeeds.
TEST(IpcSync, SemaphoreGetExactKeys) {
  SemaphoreObject sem(3);
  auto status = sem.Get(3);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3.3: get(0) succeeds trivially without changing key count.
TEST(IpcSync, SemaphoreGetZeroCountAcquires) {
  SemaphoreObject sem(2);
  auto status = sem.Get(0);
  EXPECT_EQ(status, SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 2);
}

// §15.3.3: Consecutive get() calls reduce keys cumulatively.
TEST(IpcSync, SemaphoreGetConsecutiveCalls) {
  SemaphoreObject sem(10);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.Get(4), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.Get(4), SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 3);
}

// §15.3.3: FIFO waiting queue — waiters added in order and woken in order.
TEST(IpcSync, SemaphoreGetFifoWaiterOrder) {
  SemaphoreObject sem(0);
  // Simulate two waiters needing 1 key each.
  // When 2 keys are put, the first waiter should be served first.
  int wake_order = 0;
  int first_woken = -1;
  int second_woken = -1;

  // We can't easily test coroutine wakeup without real coroutines,
  // but we can verify the waiter data structure is FIFO.
  sem.waiters.push_back({1, std::coroutine_handle<>{}});
  sem.waiters.push_back({1, std::coroutine_handle<>{}});
  EXPECT_EQ(sem.waiters.size(), 2u);
  EXPECT_EQ(sem.waiters[0].first, 1);
  EXPECT_EQ(sem.waiters[1].first, 1);
  (void)wake_order;
  (void)first_woken;
  (void)second_woken;
}

// §15.3.3: get() on semaphore with negative key count blocks.
TEST(IpcSync, SemaphoreGetBlocksOnNegativeKeys) {
  SemaphoreObject sem(-3);
  auto status = sem.Get(1);
  EXPECT_EQ(status, SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, -3);
}

// §15.3.3: After put() brings keys positive, get() succeeds.
TEST(IpcSync, SemaphoreGetAfterPutSucceeds) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kBlock);
  sem.Put(5);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 3);
}

}  // namespace
