#include <gtest/gtest.h>

#include <coroutine>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_semaphore_blocking_getter.h"
#include "simulator/awaiters.h"
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

TEST(IpcSync, SemaphorePutNegativeCountReturnsError) {
  SemaphoreObject sem(5);
  EXPECT_FALSE(sem.Put(-1));
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutZeroCountNoChange) {
  SemaphoreObject sem(5);
  EXPECT_TRUE(sem.Put(0));
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphorePutOnNegativeKeyCount) {
  SemaphoreObject sem(-5);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, -2);
  EXPECT_TRUE(sem.Put(3));
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(1), 1);
}

// §15.3.2: a process suspended waiting for keys shall execute once put() has
// returned enough keys — and not before. The getter parks needing 3 keys; a
// put() of 2 is insufficient and leaves it suspended, while the put() that
// brings the bucket to 3 resumes it.
TEST(IpcSync, SemaphorePutWakesSuspendedWaiterWhenEnoughReturned) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto getter = SpawnGetter(sem, 3, ran, 1);
  getter.h.resume();  // runs to the co_await, blocks needing 3 keys
  ASSERT_EQ(sem.waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  sem.Put(2);  // not enough — stays suspended
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.key_count, 2);

  sem.Put(1);  // bucket reaches 3 — the suspended process executes
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  getter.h.destroy();
}

// §15.3.2: the wake rule fires per put(), not per key. A single put() that
// returns enough keys for more than one suspended process shall resume every
// waiter it can satisfy — here two processes (needing 1 and 2 keys) both
// parked, and one put(3) is enough for both, so both execute in arrival order
// off that single return rather than requiring a separate put() apiece.
TEST(IpcSync, SemaphorePutSingleReturnWakesMultipleWaiters) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 2, ran, 2);
  first.h.resume();   // arrives first, needs 1, blocks
  second.h.resume();  // arrives second, needs 2, blocks
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(3);  // one return, enough for both — both processes execute
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  first.h.destroy();
  second.h.destroy();
}

}  // namespace
