#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
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

TEST(IpcSync, SemaphoreNewKeyCountIsInitialNotCap) {
  // new()'s keyCount is the starting number of keys, not an upper bound: once
  // created, the bucket may hold more keys than were initially allocated.
  SemaphoreObject sem(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(4);
  EXPECT_EQ(sem.key_count, 7);
}

TEST(IpcSync, SemaphoreNewPositiveInitialKeysProcureImmediately) {
  // §15.3.1's procure guard has an accepting side: when new() establishes a
  // positive key count, get() and try_get() may procure keys straight away with
  // no intervening put(). This isolates the value supplied at construction —
  // not a later put() — as the sole source of the positive count, the accepting
  // complement to the negative-initial-value blocking cases above.
  SemaphoreObject sem(2);
  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreNewReturnsHandle) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("s", 4);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 4);
}

// §15.3.1 (printed page 373) with §26.3 (printed 808): a semaphore declared
// through a package's typedef reached by the package scope resolution
// operator, `p::sem_t s = new(2)` on `typedef semaphore sem_t`, is created
// with the two keys its new() names, as §6.18 has the typedef name stand for
// the semaphore. get(1) takes one, try_get(2) then finds one key short and
// answers 0, and try_get(1) takes the last and answers 1: r reads 1. The
// typedef was looked up by its bare name, which the table holds only under
// "p::sem_t", so no bucket was created: get(1) blocked and r stayed 0.
TEST(SemaphoreSim, PackageQualifiedTypedefdSemaphoreHoldsItsKeys) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef semaphore sem_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  p::sem_t s = new(2);\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    s.get(1);\n"
                      "    r = s.try_get(2) * 10 + s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            1u);
}

}  // namespace
