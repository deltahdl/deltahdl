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

TEST(IpcSync, SemaphoreTryGetDefaultOne) {
  SemaphoreObject sem(1);
  int32_t result = sem.TryGet();
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreTryGetExactKeys) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
}

TEST(IpcSync, SemaphoreTryGetZeroCount) {
  SemaphoreObject sem(0);

  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3.4: a negative keyCount returns 0 and shall result in an error. The
// error is distinct from the ordinary keys-unavailable 0, so the error channel
// is set only on the negative path and the bucket is left unchanged.
TEST(IpcSync, SemaphoreTryGetNegativeCountIsError) {
  SemaphoreObject sem(5);
  bool error = false;
  EXPECT_EQ(sem.TryGet(-2, &error), 0);
  EXPECT_TRUE(error);
  EXPECT_EQ(sem.key_count, 5);
}

// The LRM prototype (function int try_get(int keyCount = 1)) carries no error
// out-parameter; the error channel is an implementation extension. Exercised
// through the bare, prototype-shaped call (no error pointer), a negative count
// must still return 0 and leave the bucket untouched — the null channel guard
// must not be dereferenced.
TEST(IpcSync, SemaphoreTryGetNegativeWithoutErrorChannelReturnsZero) {
  SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(-1), 0);
  EXPECT_EQ(sem.key_count, 5);
}

// A successful non-blocking procure is likewise not an error.
TEST(IpcSync, SemaphoreTryGetSuccessIsNotError) {
  SemaphoreObject sem(3);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 1);
  EXPECT_FALSE(error);
  EXPECT_EQ(sem.key_count, 1);
}

// §15.3.4: try_get() is the non-blocking counterpart of get(). On a bucket that
// cannot satisfy the request, get() reports a block (the caller would suspend),
// whereas try_get() returns immediately with 0 and leaves the bucket untouched.
// This contrast pins the defining "without blocking" behavior of the subclause.
TEST(IpcSync, SemaphoreTryGetDoesNotBlockWhereGetWould) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 1);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 0);
  EXPECT_FALSE(error);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetAfterPut) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(3);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetConsecutiveCalls) {
  SemaphoreObject sem(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(4), 1);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.TryGet(4), 0);
  EXPECT_EQ(sem.key_count, 3);
}

}  // namespace
