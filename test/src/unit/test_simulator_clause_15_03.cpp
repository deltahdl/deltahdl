#include <gtest/gtest.h>

#include <coroutine>

#include "fixture_simulator.h"
#include "simulator/sync_objects.h"

namespace {

// ---------------------------------------------------------------------------
// §15.3.1 new() — Semaphore construction
// ---------------------------------------------------------------------------

TEST(SemaphoreSync, NewDefaultKeyCountIsZero) {
  SemaphoreObject sem;
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, NewWithExplicitKeyCount) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(SemaphoreSync, NewWithNegativeInitialKeyCount) {
  // §15.3.1: The initial value may be negative.
  SemaphoreObject sem(-3);
  EXPECT_EQ(sem.key_count, -3);
}

// ---------------------------------------------------------------------------
// §15.3.2 put() — Return keys to the semaphore
// ---------------------------------------------------------------------------

TEST(SemaphoreSync, PutAddsKeys) {
  SemaphoreObject sem(0);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(SemaphoreSync, PutDefaultIncrementsOne) {
  SemaphoreObject sem(0);
  sem.Put();
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SemaphoreSync, PutCheckedRejectsNegativeCount) {
  // §15.3.2: A negative value shall result in an error.
  SemaphoreObject sem(5);
  EXPECT_FALSE(sem.PutChecked(-1));
  EXPECT_EQ(sem.key_count, 5);
}

TEST(SemaphoreSync, PutCheckedAcceptsZeroCount) {
  SemaphoreObject sem(3);
  EXPECT_TRUE(sem.PutChecked(0));
  EXPECT_EQ(sem.key_count, 3);
}

TEST(SemaphoreSync, PutCheckedAcceptsPositiveCount) {
  SemaphoreObject sem(0);
  EXPECT_TRUE(sem.PutChecked(4));
  EXPECT_EQ(sem.key_count, 4);
}

TEST(SemaphoreSync, PutWakesSuspendedWaiter) {
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(2, noop);
  EXPECT_EQ(sem.waiters.size(), 1u);

  sem.Put(2);
  // Waiter requesting 2 keys should have been woken and removed.
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, PutDoesNotWakeWaiterWhenInsufficientKeys) {
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(5, noop);

  sem.Put(3);
  // 3 keys not enough for waiter needing 5; waiter remains.
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.key_count, 3);
}

// ---------------------------------------------------------------------------
// §15.3.3 get() — Blocking key acquisition
// ---------------------------------------------------------------------------

TEST(SemaphoreSync, CanGetReturnsTrueWhenKeysAvailable) {
  SemaphoreObject sem(5);
  EXPECT_TRUE(sem.CanGet(3));
}

TEST(SemaphoreSync, CanGetReturnsFalseWhenInsufficientKeys) {
  SemaphoreObject sem(2);
  EXPECT_FALSE(sem.CanGet(3));
}

TEST(SemaphoreSync, CanGetDefaultChecksOneKey) {
  SemaphoreObject sem(1);
  EXPECT_TRUE(sem.CanGet());
  sem.TryGet(1);
  EXPECT_FALSE(sem.CanGet());
}

TEST(SemaphoreSync, AddWaiterRegistersForBlockingGet) {
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(3, noop);
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.waiters[0].first, 3);
}

TEST(SemaphoreSync, WaitersFifoOrder) {
  // §15.3.3: Waiting queue is FIFO — arrival order is preserved.
  // A larger request at the front blocks a smaller request behind it.
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(5, noop);  // First: needs 5 keys.
  sem.AddWaiter(1, noop);  // Second: needs 1 key.

  sem.Put(2);
  // Strict FIFO: front waiter needs 5, only 2 available → neither wakes.
  EXPECT_EQ(sem.waiters.size(), 2u);
  EXPECT_EQ(sem.key_count, 2);
}

TEST(SemaphoreSync, WaitersFifoWakesInOrder) {
  // When enough keys arrive, waiters wake front-to-back.
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(2, noop);  // First: needs 2 keys.
  sem.AddWaiter(3, noop);  // Second: needs 3 keys.

  sem.Put(6);
  // Both should be woken in order: 6 - 2 = 4, 4 - 3 = 1.
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SemaphoreSync, WaitersFifoPartialWake) {
  // Only the front waiter wakes if keys run out after serving it.
  SemaphoreObject sem(0);
  auto noop = std::noop_coroutine();
  sem.AddWaiter(2, noop);
  sem.AddWaiter(3, noop);

  sem.Put(3);
  // Front waiter (2) wakes: 3 - 2 = 1. Back waiter (3) stays: 1 < 3.
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.key_count, 1);
}

// ---------------------------------------------------------------------------
// §15.3.4 try_get() — Non-blocking key acquisition
// ---------------------------------------------------------------------------

TEST(SemaphoreSync, TryGetSucceedsWhenKeysAvailable) {
  SemaphoreObject sem(3);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SemaphoreSync, TryGetFailsWhenInsufficientKeys) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.TryGet(2), 0);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(SemaphoreSync, TryGetDefaultRequestsOneKey) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.TryGet(), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, TryGetExactKeyCountDrainsToZero) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
}

TEST(SemaphoreSync, TryGetZeroCountAlwaysSucceeds) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// ---------------------------------------------------------------------------
// Context integration
// ---------------------------------------------------------------------------

TEST(SemaphoreSync, ContextCreateAndFind) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("sem1", 3);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 3);

  auto* found = f.ctx.FindSemaphore("sem1");
  EXPECT_EQ(found, sem);
}

TEST(SemaphoreSync, ContextFindReturnsNullForUnknown) {
  SyncFixture f;
  EXPECT_EQ(f.ctx.FindSemaphore("no_such_sem"), nullptr);
}

TEST(SemaphoreSync, MultipleSemaphoresInContext) {
  SyncFixture f;
  auto* sem1 = f.ctx.CreateSemaphore("s1", 1);
  auto* sem2 = f.ctx.CreateSemaphore("s2", 5);
  EXPECT_EQ(sem1->key_count, 1);
  EXPECT_EQ(sem2->key_count, 5);
  EXPECT_NE(f.ctx.FindSemaphore("s1"), f.ctx.FindSemaphore("s2"));
}

TEST(SemaphoreSync, MultiplePutTryGetCyclesDrainKeys) {
  SemaphoreObject sem(0);
  sem.Put(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(7), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, MultiplePutTryGetCyclesRefillAndDrain) {
  SemaphoreObject sem(0);
  sem.Put(10);
  sem.TryGet(10);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, KeyCountCanExceedInitial) {
  // §15.3.1: Key count can increase beyond initial keyCount.
  SemaphoreObject sem(1);
  sem.Put(10);
  EXPECT_EQ(sem.key_count, 11);
}

TEST(SemaphoreSync, LargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(SemaphoreSync, NegativeInitialRequiresPutBeforeGet) {
  // §15.3.1: Keys must be positive before get()/try_get() can procure.
  SemaphoreObject sem(-2);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(3);
  // -2 + 3 = 1.
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
}

}  // namespace
