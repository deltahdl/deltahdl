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

TEST(IpcSync, SemaphoreTryGetNegativeCountIsError) {
  delta::SemaphoreObject sem(5);
  bool error = false;
  EXPECT_EQ(sem.TryGet(-2, &error), 0);
  EXPECT_TRUE(error);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphoreTryGetNegativeWithoutErrorChannelReturnsZero) {
  delta::SemaphoreObject sem(5);
  EXPECT_EQ(sem.TryGet(-1), 0);
  EXPECT_EQ(sem.key_count, 5);
}

TEST(IpcSync, SemaphoreTryGetSuccessIsNotError) {
  delta::SemaphoreObject sem(3);
  bool error = false;
  EXPECT_EQ(sem.TryGet(2, &error), 1);
  EXPECT_FALSE(error);
  EXPECT_EQ(sem.key_count, 1);
}

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
