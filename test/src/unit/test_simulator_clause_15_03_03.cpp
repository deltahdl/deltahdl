#include <gtest/gtest.h>

#include <coroutine>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_semaphore_blocking_getter.h"
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

// §15.3.3: a get() with more keys required than available blocks until the
// keys become available; the process then runs. Two processes block on an
// empty bucket; each put() of one key releases the head of the queue in turn.
TEST(IpcSync, SemaphoreGetBlocksThenRunsInArrivalOrder) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 1, ran, 2);
  first.h.resume();   // arrives first, blocks
  second.h.resume();  // arrives second, blocks
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(1);  // releases the earliest arrival
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);

  sem.Put(1);  // releases the next
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);

  first.h.destroy();
  second.h.destroy();
}

// §15.3.3: the waiting queue is FIFO and arrival order shall be preserved. The
// earliest arrival requires two keys; a process that arrived later requiring a
// single key must not be served ahead of it. A lone key satisfies neither, and
// once two keys are available the head runs first, then the later arrival.
TEST(IpcSync, SemaphoreGetFifoPreservesArrivalOrderUnderHeadOfLine) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto head = SpawnGetter(sem, 2, ran, 1);   // first in, needs 2
  auto later = SpawnGetter(sem, 1, ran, 2);  // second in, needs 1
  head.h.resume();
  later.h.resume();
  ASSERT_EQ(sem.waiters.size(), 2u);

  sem.Put(1);  // one key available, but head needs 2; FIFO holds the later,
               // single-key request behind it rather than letting it jump ahead
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.key_count, 1);

  sem.Put(1);  // bucket reaches 2 — the head runs and consumes both keys
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(sem.key_count, 0);
  ASSERT_EQ(sem.waiters.size(), 1u);

  sem.Put(1);  // the later arrival is served next
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());

  head.h.destroy();
  later.h.destroy();
}

}  // namespace
