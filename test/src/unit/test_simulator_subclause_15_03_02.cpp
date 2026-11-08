#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "helpers_semaphore_blocking_getter.h"
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

TEST(IpcSync, SemaphorePutWakesSuspendedWaiterWhenEnoughReturned) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto getter = SpawnGetter(sem, 3, ran, 1);
  getter.h.resume();
  ASSERT_EQ(sem.waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  sem.Put(2);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.key_count, 2);

  sem.Put(1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  getter.h.destroy();
}

TEST(IpcSync, SemaphorePutSingleReturnWakesMultipleWaiters) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 2, ran, 2);
  first.h.resume();
  second.h.resume();
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(3);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  first.h.destroy();
  second.h.destroy();
}

TEST(SemaphoreSim, PutInsideAFunctionReturnsAKey) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore s = new(0);\n"
                      "  int y;\n"
                      "  function void give();\n"
                      "    s.put(1);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    give();\n"
                      "    y = s.try_get(1) * 10 + s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(SemaphoreSim, GetInsideAFunctionTakesAKey) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore s = new(2);\n"
                      "  int y;\n"
                      "  function void take();\n"
                      "    s.get(1);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    take();\n"
                      "    y = s.try_get(2) * 10 + s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(SemaphoreSim, GetInsideAFunctionLeavesTheBucketEmptyUntilPut) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore s = new(2);\n"
                      "  int y;\n"
                      "  function void drain();\n"
                      "    s.get(2);\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    drain();\n"
                      "    y = 2 + s.try_get(1) * 10;\n"
                      "    s.put(1);\n"
                      "    y = y + s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

TEST(SemaphoreSim, GetInsideAFunctionWithTooFewKeysIsAnError) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  semaphore s = new(2);\n"
      "  int y;\n"
      "  function void take();\n"
      "    s.get(3);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    take();\n"
      "    y = s.try_get(2);\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "semaphore get(): 's' has too few keys, so the "
                            "call would block inside a function",
                            5, "13.4"));
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SemaphoreSim, PropertyGetInsideAMethodTakesTheObjectsKey) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s = new(1);\n"
                      "  function void take();\n"
                      "    s.get(1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.take();\n"
                      "    y = c.s.try_get(1) * 10 + 5;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

TEST(SemaphoreSim, PutWithANegativeCountIsReported) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore s = new(1);\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.put(-1);\n"
      "    r = s.try_get(2) * 10 + s.try_get();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "semaphore put(): the key count -1 is negative", 5,
                            "15.3.2"));
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
