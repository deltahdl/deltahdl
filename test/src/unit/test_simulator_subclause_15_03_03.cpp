#include <gtest/gtest.h>

#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_semaphore_blocking_getter.h"
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

TEST(IpcSync, SemaphoreGetBlocksThenRunsInArrivalOrder) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 1, ran, 2);
  first.h.resume();
  second.h.resume();
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);

  sem.Put(1);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);

  first.h.destroy();
  second.h.destroy();
}

TEST(IpcSync, SemaphoreGetFifoPreservesArrivalOrderUnderHeadOfLine) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto head = SpawnGetter(sem, 2, ran, 1);
  auto later = SpawnGetter(sem, 1, ran, 2);
  head.h.resume();
  later.h.resume();
  ASSERT_EQ(sem.waiters.size(), 2u);

  sem.Put(1);
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.key_count, 1);

  sem.Put(1);
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(sem.key_count, 0);
  ASSERT_EQ(sem.waiters.size(), 1u);

  sem.Put(1);
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());

  head.h.destroy();
  later.h.destroy();
}

TEST(IpcSync, SemaphoreGetImmediateAcquireContinuesWithoutBlocking) {
  SemaphoreObject sem(5);
  std::vector<int> ran;
  auto getter = SpawnGetter(sem, 3, ran, 1);
  getter.h.resume();
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 2);

  getter.h.destroy();
}

TEST(SemaphoreSim, GetInAClassTaskResumesOnItsOwnObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class Worker;\n"
      "    int id, got;\n"
      "    semaphore s;\n"
      "    function new(int i); id = i; s = new(0); endfunction\n"
      "    task run();\n"
      "      s.get();\n"
      "      got = this.id * 10 + ($time == 4);\n"
      "    endtask\n"
      "  endclass\n"
      "  Worker w;\n"
      "  int r;\n"
      "  initial begin\n"
      "    w = new(7);\n"
      "    fork\n"
      "      w.run();\n"
      "      #4 w.s.put();\n"
      "    join\n"
      "    r = w.got;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 71u);
}

TEST(SemaphoreSim, GetWithANegativeCountIsReported) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore s = new(0);\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.get(-1);\n"
      "    r = 5 + $time;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "semaphore get(): the key count -1 is negative", 5,
                            "15.3.3"));
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(IpcSync, AWaitingCallThroughACallsResultRunsTheCallOnce) {
  SimFixture f;
  auto out = RunCapture(
      "class K;\n"
      "  mailbox #(int) mb = new;\n"
      "  semaphore s = new(2);\n"
      "endclass\n"
      "module t;\n"
      "  int calls = 0, x, y, c1, c2, c3, c4;\n"
      "  K k = new;\n"
      "  function K pk(); calls++; return k; endfunction\n"
      "  initial begin\n"
      "    pk().mb.put(5);\n"
      "    c1 = calls;\n"
      "    pk().mb.peek(y);\n"
      "    c2 = calls;\n"
      "    pk().mb.get(x);\n"
      "    c3 = calls;\n"
      "    pk().s.get(2);\n"
      "    c4 = calls;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", c1, c2, c3, c4, y, x, "
      "k.s.try_get(1));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 4 5 5 0\n");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
