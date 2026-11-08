#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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
  SemaphoreObject sem(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(4);
  EXPECT_EQ(sem.key_count, 7);
}

TEST(IpcSync, SemaphoreNewPositiveInitialKeysProcureImmediately) {
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

TEST(SemaphoreSim, ClassPropertySemaphoreHoldsItsKeys) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s = new(2);\n"
                      "  task probe(output int r);\n"
                      "    s.get(1);\n"
                      "    r = s.try_get(2) * 10 + s.try_get(1);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.probe(y);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(SemaphoreSim, TwoObjectsHoldSeparateSemaphores) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s = new(1);\n"
                      "  function int take();\n"
                      "    return s.try_get(1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    y = c1.take() * 10 + c2.take();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

TEST(SemaphoreSim, ThisAndHandleQualifiedPropertySemaphoreReceivers) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s = new;\n"
                      "  function void give();\n"
                      "    this.s.put(2);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.give();\n"
                      "    y = c.s.try_get(2) * 10 + c.s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(SemaphoreSim, PropertySemaphoreGetWaitsForTheModulesPut) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s = new;\n"
                      "  task take();\n"
                      "    s.get(1);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module top;\n"
                      "  int at;\n"
                      "  C c;\n"
                      "  initial begin\n"
                      "    c = new;\n"
                      "    fork\n"
                      "      begin\n"
                      "        c.take();\n"
                      "        at = $time + 10;\n"
                      "      end\n"
                      "      #5 c.s.put(1);\n"
                      "    join\n"
                      "  end\n"
                      "endmodule\n",
                      "at"),
            15u);
}

TEST(SemaphoreSim, PutThroughANullPropertySemaphoreIsReported) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  semaphore s;\n"
      "  function void give();\n"
      "    s.put(1);\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.give();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' called through the null handle 's'",
                            4, "8.4"));
}

TEST(SemaphoreSim, AutomaticLocalSemaphoresHoldTheirOwnBuckets) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int r, a, b, m;\n"
                      "  task automatic count(int keys, output int n);\n"
                      "    semaphore s = new(keys);\n"
                      "    n = 0;\n"
                      "    while (s.try_get()) n++;\n"
                      "  endtask\n"
                      "  task automatic count2(int keys, output int n);\n"
                      "    semaphore s;\n"
                      "    s = new(keys);\n"
                      "    n = 0;\n"
                      "    while (s.try_get()) n++;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    count(2, a);\n"
                      "    count2(3, b);\n"
                      "    begin\n"
                      "      automatic semaphore s2 = new(4);\n"
                      "      m = 0;\n"
                      "      while (s2.try_get()) m++;\n"
                      "    end\n"
                      "    r = a * 100 + b * 10 + m;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            234u);
}

TEST(SemaphoreSim, NewAfterAHandleCopyLeavesTheOtherNamesBucket) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore a = new(1);\n"
                      "  semaphore b;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    b = a;\n"
                      "    b = new(5);\n"
                      "    r = a.try_get(2) * 10 + b.try_get(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            1u);
}

TEST(SemaphoreSim, LoopGenerateSemaphoreNewReadsItsInstanceIndex) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  int r;\n"
                      "  for (genvar i = 0; i < 2; i++) begin : g\n"
                      "    semaphore s = new(i + 1);\n"
                      "    int got;\n"
                      "    initial got = s.try_get() * 10 + s.try_get();\n"
                      "  end\n"
                      "  initial #1 r = g[0].got * 100 + g[1].got;\n"
                      "endmodule\n",
                      "r"),
            1011u);
}

TEST(SemaphoreSim, FixedArrayElementIsGivenItsSemaphore) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  semaphore arr[2];\n"
                       "  int a, b;\n"
                       "  initial begin\n"
                       "    arr[1] = new(1);\n"
                       "    a = arr[1].try_get(1);\n"
                       "    b = arr[1].try_get(1);\n"
                       "    $display(\"a=%0d b=%0d\", a, b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=1 b=0\n");
}

}  // namespace
