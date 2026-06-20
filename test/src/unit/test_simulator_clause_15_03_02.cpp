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

}  // namespace
