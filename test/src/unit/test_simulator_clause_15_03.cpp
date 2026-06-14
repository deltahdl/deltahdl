#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/awaiters.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"

namespace {

TEST(IpcSync, SemaphoreContextCreateFind) {
  SyncFixture f;
  auto* sem = f.ctx.CreateSemaphore("sem1", 3);
  ASSERT_NE(sem, nullptr);
  EXPECT_EQ(sem->key_count, 3);

  auto* found = f.ctx.FindSemaphore("sem1");
  EXPECT_EQ(found, sem);

  auto* not_found = f.ctx.FindSemaphore("no_such_sem");
  EXPECT_EQ(not_found, nullptr);
}

TEST(IpcSync, SemaphoreMultiplePutTryGetCycles_DrainKeys) {
  SemaphoreObject sem(0);
  sem.Put(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(7), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreMultiplePutTryGetCycles_RefillAndDrain) {
  SemaphoreObject sem(0);
  sem.Put(10);
  sem.TryGet(10);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(2);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreLargeKeyCount) {
  SemaphoreObject sem(1000000);
  EXPECT_EQ(sem.TryGet(999999), 1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.TryGet(2), 0);
  sem.Put(1);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreMutualExclusionPattern) {
  SemaphoreObject sem(1);

  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);

  EXPECT_EQ(sem.TryGet(1), 0);
  EXPECT_EQ(sem.key_count, 0);

  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);

  EXPECT_EQ(sem.TryGet(1), 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreKeyCountCanExceedInitial) {
  SemaphoreObject sem(2);
  sem.Put(3);
  EXPECT_EQ(sem.key_count, 5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: a process procures keys from the bucket before it continues. When the
// bucket holds at least the requested number of keys, the blocking procure
// succeeds immediately and drains the bucket by that amount.
TEST(IpcSync, SemaphoreGetAcquiresWhenKeysAvailable) {
  SemaphoreObject sem(2);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: a process that cannot procure the required number of keys is not
// allowed to continue and must wait. The blocking procure reports that the
// caller blocks and leaves the bucket untouched, so only a fixed number of
// processes hold keys at once.
TEST(IpcSync, SemaphoreGetBlocksWhenKeysInsufficient) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: a waiting process proceeds only once a sufficient number of keys has
// been returned to the bucket. A procure that blocks for lack of keys succeeds
// after enough keys are put back.
TEST(IpcSync, SemaphoreWaiterProceedsAfterKeysReturned) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kBlock);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 2);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: the requirement is that a waiter proceeds only once a *sufficient*
// number of keys is back in the bucket. A return that is too small to cover the
// outstanding request leaves the procure unsatisfiable; the procure succeeds
// only after enough additional keys are returned to reach the requested amount.
TEST(IpcSync, SemaphoreWaiterRemainsBlockedUntilEnoughKeysReturned) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kBlock);

  // A partial return below the requested count is still not enough to procure.
  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kBlock);

  // Once the bucket finally holds the full requested amount, the procure wins.
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3: only a fixed number of holders may hold keys at once — with N keys in
// the bucket, N procurements of one key each succeed and the very next one must
// block, modelling the cap on simultaneous progress. Returning a key lets one
// more blocked procurement go through.
TEST(IpcSync, SemaphoreLimitsConcurrentHoldersToKeyCount) {
  SemaphoreObject sem(2);

  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);

  // The bucket is empty: a third holder cannot procure and must wait.
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);

  // One key returned admits exactly one more holder, then the cap binds again.
  sem.Put(1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
}

}
