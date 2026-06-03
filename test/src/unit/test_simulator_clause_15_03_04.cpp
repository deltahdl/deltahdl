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

// The keys-unavailable path also returns 0, but it is not an error: a caller
// observing the error channel must be able to tell the two zero results apart.
TEST(IpcSync, SemaphoreTryGetUnavailableIsNotError) {
  SemaphoreObject sem(1);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 0);
  EXPECT_FALSE(error);
  EXPECT_EQ(sem.key_count, 1);
}

// A successful non-blocking procure is likewise not an error.
TEST(IpcSync, SemaphoreTryGetSuccessIsNotError) {
  SemaphoreObject sem(3);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 1);
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

}
