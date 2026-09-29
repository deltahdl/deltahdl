#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/sync_objects.h"

using namespace delta;

namespace {

TEST(IpcSync, SemaphoreTryGetDefaultOne) {
  delta::SemaphoreObject sem(1);
  int32_t result = sem.TryGet();
  EXPECT_EQ(result, 1);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreTryGetExactKeys) {
  delta::SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(5), 1);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.TryGet(1), 0);
}

TEST(IpcSync, SemaphoreTryGetZeroCount) {
  delta::SemaphoreObject sem(0);

  EXPECT_EQ(sem.TryGet(0), 1);
  EXPECT_EQ(sem.key_count, 0);
}

// §15.3.4: a negative keyCount returns 0 and shall result in an error. The
// error is distinct from the ordinary keys-unavailable 0, so the error channel
// is set only on the negative path and the bucket is left unchanged.
TEST(IpcSync, SemaphoreTryGetNegativeCountIsError) {
  delta::SemaphoreObject sem(5);
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
  delta::SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(-1), 0);
  EXPECT_EQ(sem.key_count, 5);
}

// A successful non-blocking procure is likewise not an error.
TEST(IpcSync, SemaphoreTryGetSuccessIsNotError) {
  delta::SemaphoreObject sem(3);
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
  delta::SemaphoreObject sem(1);
  EXPECT_EQ(sem.Get(2), delta::SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 1);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 0);
  EXPECT_FALSE(error);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetAfterPut) {
  delta::SemaphoreObject sem(0);
  EXPECT_EQ(sem.TryGet(1), 0);
  sem.Put(3);
  EXPECT_EQ(sem.TryGet(2), 1);
  EXPECT_EQ(sem.key_count, 1);
}

TEST(IpcSync, SemaphoreTryGetConsecutiveCalls) {
  delta::SemaphoreObject sem(10);
  EXPECT_EQ(sem.TryGet(3), 1);
  EXPECT_EQ(sem.key_count, 7);
  EXPECT_EQ(sem.TryGet(4), 1);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.TryGet(4), 0);
  EXPECT_EQ(sem.key_count, 3);
}

// §15.3.4 with §13.5.2: a `ref semaphore` formal is the actual itself, so the
// body's try_get() takes the one key the caller's bucket holds and then finds
// none, read as 10. Bound to no bucket, the formal answered 0 twice.
TEST(SemaphoreSim, TryGetThroughARefFormalDrainsTheCallersBucket) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore s = new(1);\n"
      "  task automatic probe(ref semaphore sm, output int a, output int b);\n"
      "    a = sm.try_get(); b = sm.try_get();\n"
      "  endtask\n"
      "  int r1, r2, r;\n"
      "  initial begin\n"
      "    probe(s, r1, r2);\n"
      "    r = r1 * 10 + r2;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §15.3.4 (printed page 374): a negative key count handed to try_get() is an
// error, reported at the call, and try_get() returns 0 taking no key, which
// the plain try_get() after it then takes: 0 and 1, read as 1.
TEST(SemaphoreSim, TryGetWithANegativeCountIsReportedAndAnswersZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore s = new(1);\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = s.try_get(-1) * 10 + s.try_get();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "semaphore try_get(): the key count -1 is negative",
                            5, "15.3.4"));
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
