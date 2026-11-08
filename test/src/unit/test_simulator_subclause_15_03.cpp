#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/stmt_exec.h"
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

TEST(IpcSync, SemaphoreGetAcquiresWhenKeysAvailable) {
  SemaphoreObject sem(2);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreGetBlocksWhenKeysInsufficient) {
  SemaphoreObject sem(1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreWaiterProceedsAfterKeysReturned) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kBlock);
  sem.Put(2);
  EXPECT_EQ(sem.key_count, 2);
  EXPECT_EQ(sem.Get(2), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreWaiterRemainsBlockedUntilEnoughKeysReturned) {
  SemaphoreObject sem(0);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kBlock);

  sem.Put(1);
  EXPECT_EQ(sem.key_count, 1);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kBlock);

  sem.Put(2);
  EXPECT_EQ(sem.key_count, 3);
  EXPECT_EQ(sem.Get(3), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
}

TEST(IpcSync, SemaphoreLimitsConcurrentHoldersToKeyCount) {
  SemaphoreObject sem(2);

  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);

  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);

  sem.Put(1);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kAcquired);
  EXPECT_EQ(sem.key_count, 0);
  EXPECT_EQ(sem.Get(1), SemGetStatus::kBlock);
}

TEST(SemaphoreSim, NewFillsBucketSoTryGetSucceeds) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(2);\n"
      "  logic [31:0] got;\n"
      "  initial got = sem.try_get(1);\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SemaphoreSim, TryGetOnEmptyBucketProcuresNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(0);\n"
      "  logic [31:0] got;\n"
      "  initial got = sem.try_get(1);\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SemaphoreSim, NewAssignmentFillsBucket) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem;\n"
      "  logic [31:0] got;\n"
      "  initial begin\n"
      "    sem = new(3);\n"
      "    got = sem.try_get(3);\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SemaphoreSim, GetProcuresAvailableKeysWithoutWaiting) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(1);\n"
      "  logic [31:0] took;\n"
      "  initial begin\n"
      "    #3 sem.get(1);\n"
      "    took = $time;\n"
      "  end\n"
      "endmodule\n",
      f, "took");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(SemaphoreSim, GetWaitsUntilKeysAreReturned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(1);\n"
      "  logic [31:0] took;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    #5 sem.put(1);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 sem.get(1);\n"
      "    took = $time;\n"
      "  end\n"
      "endmodule\n",
      f, "took");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(SemaphoreSim, GetWaitsForASufficientNumberOfKeys) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(0);\n"
      "  logic [31:0] took;\n"
      "  initial begin\n"
      "    #2 sem.put(1);\n"
      "    #4 sem.put(1);\n"
      "  end\n"
      "  initial begin\n"
      "    sem.get(2);\n"
      "    took = $time;\n"
      "  end\n"
      "endmodule\n",
      f, "took");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(SemaphoreSim, OneKeyAdmitsOneProcessAtATime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(1);\n"
      "  logic [31:0] holders;\n"
      "  logic [31:0] overlaps;\n"
      "  initial begin holders = 0; overlaps = 0; end\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    holders = holders + 1;\n"
      "    if (holders > 1) overlaps = overlaps + 1;\n"
      "    #4 holders = holders - 1;\n"
      "    sem.put(1);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 sem.get(1);\n"
      "    holders = holders + 1;\n"
      "    if (holders > 1) overlaps = overlaps + 1;\n"
      "    holders = holders - 1;\n"
      "    sem.put(1);\n"
      "  end\n"
      "endmodule\n",
      f, "overlaps");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SemaphoreSim, ChildInstanceBucketAnswersItsBareName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  semaphore s;\n"
      "  int gets, first, second, r;\n"
      "  initial begin\n"
      "    gets = 0;\n"
      "    s = new(0);\n"
      "    s.put(2);\n"
      "    s.get(1);\n"
      "    gets = gets + 1;\n"
      "    first = s.try_get(1);\n"
      "    second = s.try_get(1);\n"
      "    r = gets * 100 + first * 10 + second;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 110u);
}

TEST(SemaphoreSim, TypedefdSemaphorePropertyHoldsItsKeys) {
  EXPECT_EQ(RunAndGet("typedef semaphore sem_t;\n"
                      "class C;\n"
                      "  sem_t s = new(1);\n"
                      "  function int take();\n"
                      "    return s.try_get(1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int a, b, y;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    a = c.take();\n"
                      "    b = c.take();\n"
                      "    y = a * 10 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(SemaphoreSim, StaticSemaphorePropertyIsSharedByEveryObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static semaphore s = new(1);\n"
                      "  function int take();\n"
                      "    return s.try_get(1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int a, b, c, y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    a = c1.take();\n"
                      "    b = c2.take();\n"
                      "    C::s.put(1);\n"
                      "    c = c2.take();\n"
                      "    y = a * 100 + b * 10 + c;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            101u);
}

TEST(SemaphoreSim, ConstructorTakesTheModulesSemaphoreAsAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore s;\n"
                      "  function new(semaphore sem);\n"
                      "    s = sem;\n"
                      "  endfunction\n"
                      "  function int take();\n"
                      "    return s.try_get(1);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  semaphore shared = new(1);\n"
                      "  int a, b, c, y;\n"
                      "  initial begin\n"
                      "    static C c1 = new(shared);\n"
                      "    static C c2 = new(shared);\n"
                      "    a = c1.take();\n"
                      "    b = c2.take();\n"
                      "    shared.put(1);\n"
                      "    c = c2.take();\n"
                      "    y = a * 100 + b * 10 + c;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            101u);
}

TEST(SemaphoreSim, PropertySemaphoreComparesWithNullByTheObjectItHolds) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore held;\n"
                      "  semaphore spare;\n"
                      "  function new(semaphore sem);\n"
                      "    held = sem;\n"
                      "  endfunction\n"
                      "  function int probe();\n"
                      "    int r = 0;\n"
                      "    if (held != null) r = r + 1;\n"
                      "    if (spare == null) r = r + 10;\n"
                      "    if (held) r = r + 100;\n"
                      "    return r;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  semaphore shared = new(1);\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c = new(shared);\n"
                      "    y = c.probe();\n"
                      "    if (c.held != null) y = y + 1000;\n"
                      "    c.spare = new(2);\n"
                      "    if (c.spare != null) y = y + 10000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11111u);
}

TEST(SemaphoreSim, NestedClassMethodTakesTheEnclosingClassStaticSemaphore) {
  EXPECT_EQ(RunAndGet("class Outer;\n"
                      "  static semaphore s = new(1);\n"
                      "  class Inner;\n"
                      "    function int take();\n"
                      "      return s.try_get(1);\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endclass\n"
                      "module top;\n"
                      "  int a, b, y;\n"
                      "  initial begin\n"
                      "    static Outer::Inner i = new;\n"
                      "    a = i.take();\n"
                      "    b = Outer::s.try_get(1);\n"
                      "    y = a * 10 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

std::string StaticSemaphoreKeyedByUnitSrc(const std::string& head,
                                          const std::string& type) {
  return "int keys = 1;\n" + head + "class C;\n  static " + type +
         " s = new(keys);\n"
         "endclass\n"
         "module top;\n"
         "  int first, second, r;\n"
         "  initial begin\n"
         "    keys = 3;\n"
         "    first = C::s.try_get(1);\n"
         "    second = C::s.try_get(1);\n"
         "    r = first * 10 + second;\n"
         "  end\n"
         "endmodule\n";
}

TEST(SemaphoreSim, StaticSemaphorePropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticSemaphoreKeyedByUnitSrc("", "semaphore"), "r"),
            10u);
}

TEST(SemaphoreSim,
     StaticTypedefdSemaphorePropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticSemaphoreKeyedByUnitSrc(
                          "typedef semaphore sem_t;\n", "sem_t"),
                      "r"),
            10u);
}

TEST(SemaphoreSim, ModuleSemaphoreVariableIsNullUntilNew) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore unset;\n"
                      "  semaphore filled = new(1);\n"
                      "  semaphore copy;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    r = 0;\n"
                      "    if (unset == null) r = r + 1;\n"
                      "    if (unset) r = r + 10;\n"
                      "    if (filled != null) r = r + 100;\n"
                      "    if (filled) r = r + 1000;\n"
                      "    unset = new(2);\n"
                      "    if (unset != null) r = r + 10000;\n"
                      "    if (unset == null) r = r + 100000;\n"
                      "    copy = filled;\n"
                      "    if (copy != null) r = r + 1000000;\n"
                      "    filled = null;\n"
                      "    if (filled == null) r = r + 10000000;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            11011101u);
}

TEST(SemaphoreSim, ModuleSemaphoreNewInProcessFillsTheBucketItMakesHeld) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  semaphore bare;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    bare = new(2);\n"
                      "    y = bare.try_get(1) * 100 + bare.try_get(1) * 10 +\n"
                      "        bare.try_get(1);\n"
                      "    if (bare != null) y = y + 1000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1110u);
}

TEST(SemaphoreSim, SemaphoreHandlesCompareByTheBucketEachRefersTo) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  semaphore p = new(1);\n"
                      "  semaphore q = new(1);\n"
                      "endclass\n"
                      "module top;\n"
                      "  semaphore first = new(1);\n"
                      "  semaphore second = new(1);\n"
                      "  semaphore third;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C o = new;\n"
                      "    y = 0;\n"
                      "    if (first != second) y = y + 1;\n"
                      "    third = first;\n"
                      "    if (third == first) y = y + 10;\n"
                      "    if (third == second) y = y + 100;\n"
                      "    if (o.p != o.q) y = y + 1000;\n"
                      "    o.q = o.p;\n"
                      "    if (o.p != o.q) y = y + 10000;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1011u);
}

TEST(SemaphoreSim, HandleAssignedAtModuleScopeSharesTheBucket) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore a = new(1);\n"
      "  semaphore b;\n"
      "  int r;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    b.put();\n"
      "    r = a.try_get(2);\n"
      "    a.put(2);\n"
      "    b = null;\n"
      "    r = r * 10 + a.try_get(2);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(SemaphoreSim, InterfaceSemaphoreReachedThroughTheInstance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "interface bus;\n"
      "  semaphore s;\n"
      "  task grab(); s.get(); endtask\n"
      "endinterface\n"
      "module t;\n"
      "  bus b();\n"
      "  int r1, r2, at, r;\n"
      "  initial begin\n"
      "    b.s = new(1);\n"
      "    r1 = b.s.try_get(); r2 = b.s.try_get();\n"
      "    fork\n"
      "      begin b.grab(); at = $time; end\n"
      "      #3 b.s.put();\n"
      "    join\n"
      "    r = r1 * 100 + r2 * 10 + at;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 103u);
}

TEST(SemaphoreSim, GenerateBlockSemaphoreReachedByItsPath) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    semaphore s = new(i + 1);\n"
      "  end\n"
      "  initial r = g[1].s.try_get(2) * 10 + g[1].s.try_get(2);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SemaphoreSim, MethodsCalledWithoutAnArgumentListActOnTheBucket) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore s;\n"
      "  int r, at, v;\n"
      "  initial begin\n"
      "    s = new;\n"
      "    s.put;\n"
      "    r = s.try_get;\n"
      "    fork\n"
      "      begin s.get; at = $time; end\n"
      "      #2 s.put;\n"
      "    join\n"
      "    v = r * 10 + at;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(SemaphoreSim, ClassExtendingTheSemaphoreHoldsTheBaseBucket) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class CountingSem extends semaphore;\n"
      "    int taken;\n"
      "    function new(int k); super.new(k); taken = 0; endfunction\n"
      "    function int grab();\n"
      "      int r; r = try_get(); if (r) taken++; return r;\n"
      "    endfunction\n"
      "  endclass\n"
      "  CountingSem cs;\n"
      "  int r1, r2, r3, r;\n"
      "  initial begin\n"
      "    cs = new(1);\n"
      "    r1 = cs.grab(); r2 = cs.grab();\n"
      "    cs.put();\n"
      "    r3 = cs.try_get();\n"
      "    r = r1 * 1000 + r2 * 100 + cs.taken * 10 + r3;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1011u);
}

TEST(SemaphoreSim, ElementsOfContainersOfSemaphoresHoldTheirBuckets) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore q[$];\n"
      "  semaphore m[string];\n"
      "  semaphore t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    t = new(2); q.push_back(t);\n"
      "    t = new(1); q.push_back(t);\n"
      "    m[\"a\"] = new(1); m[\"b\"] = new(2);\n"
      "    r = q[0].try_get();\n"
      "    r = r * 10 + q[1].try_get();\n"
      "    r = r * 10 + q[1].try_get();\n"
      "    r = r * 10 + q[0].try_get();\n"
      "    r = r * 10 + m[\"a\"].try_get();\n"
      "    r = r * 10 + m[\"b\"].try_get();\n"
      "    r = r * 10 + m[\"a\"].try_get();\n"
      "    r = r * 10 + m[\"b\"].try_get();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11011101u);
}

}  // namespace
