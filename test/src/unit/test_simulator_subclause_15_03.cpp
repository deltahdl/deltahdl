#include <gtest/gtest.h>

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

// The tests above drive SemaphoreObject from C++. The ones below state the
// same rule as SystemVerilog, which is where §15.3 makes its claim: a process
// procures its keys from the bucket before it continues, and waits where it
// stands until enough keys have been returned.

// §15.3.1 with §15.3.4: new() puts the keys it names into the bucket, and a
// try_get() that finds them there procures them.
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

// §15.3.4: a try_get() that finds the bucket short of keys procures none and
// says so, rather than waiting.
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

// §15.3.1: the bucket may also be built by an assignment rather than by a
// declaration initializer, and the keys reach it either way.
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

// §15.3: a get() that finds its keys in the bucket procures them and the
// process continues, so the statement after it runs at the time the get() was
// reached.
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

// §15.3: "all others shall wait until a sufficient number of keys are returned
// to the bucket". The one key is held from time 0, so the second process
// reaches its get() at time 1 and cannot pass it until the put() at time 5.
// The time it recorded is what says it waited: a get() that did not wait would
// have recorded 1.
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

// §15.3: the wait ends when *enough* keys are back, not when any key is. Two
// are asked for and returned one at a time, so the waiting process passes at
// the second put() and not the first.
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

// §15.3: only as many processes as there are keys are in progress at once.
// Each of the two processes here holds the single key across a delay, so the
// second cannot enter until the first has returned it and the two stretches
// cannot overlap.
TEST(SemaphoreSim, OneKeyAdmitsOneProcessAtATime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  semaphore sem = new(1);\n"
      "  logic [31:0] inside;\n"
      "  logic [31:0] overlaps;\n"
      "  initial begin inside = 0; overlaps = 0; end\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    inside = inside + 1;\n"
      "    if (inside > 1) overlaps = overlaps + 1;\n"
      "    #4 inside = inside - 1;\n"
      "    sem.put(1);\n"
      "  end\n"
      "  initial begin\n"
      "    #1 sem.get(1);\n"
      "    inside = inside + 1;\n"
      "    if (inside > 1) overlaps = overlaps + 1;\n"
      "    inside = inside - 1;\n"
      "    sem.put(1);\n"
      "  end\n"
      "endmodule\n",
      f, "overlaps");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §15.3 in an instantiated module: `semaphore s` declared in M, which top
// instantiates as `m`, is created under "m.s", and §23.9 resolves the bare
// name `s` inside M through the instance. The lookup
// (SimContext::FindSemaphore) asked for the bare key alone, so `s = new(0)`
// filled no bucket, put() and get() ran on no semaphore, and try_get() was
// served by none. The bucket starts empty, put() returns two keys, get()
// procures one without waiting so the count after it is 1, the first try_get()
// procures the last key and the second finds none: 1, 1, 0 read as 110.
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

// §15.3.1 (printed page 373) with §6.18 (printed 118) and §8.7 (printed
// 184): a class property declared through `typedef semaphore sem_t` is a
// semaphore as one declared `semaphore s` is, built per object with the one
// key its `new(1)` names, so the object's first try_get(1) procures it and
// the second finds none: 1 and 0 read as 10. The run held no table of what
// a typedef stands for, so the property was of no type it knew: its `new`
// filled no bucket and try_get() was called through a null handle.
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
                      "    C c = new;\n"
                      "    a = c.take();\n"
                      "    b = c.take();\n"
                      "    y = a * 10 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §8.9 (printed page 186) with §15.3.1 (printed 373): a static semaphore
// property is one bucket shared by every object of the class, so the one
// key c1's try_get(1) procures leaves c2's try_get(1) nothing, and the
// module's `C::s.put(1)` returns it for c2's next try_get(1): 1, 0 and 1
// read as 101. Two buckets would have read 111, and the run's tables, which
// the static property was left to, held none.
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
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
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

// §15.3 (printed page 373) with §13.5.1 (printed 348) and §8.2 (printed
// 180): a semaphore variable is a handle to the bucket, passed by value as
// the handle, so a constructor's `s = sem` on a `semaphore sem` formal makes
// the property a handle to the module's bucket and two objects built on it
// share its one key: c1's try_get(1) procures it, c2's finds none, and the
// module's `shared.put(1)` returns it for c2, 101. The assignment fell to
// the generic store, so the property stayed null and take() was reported as
// a call through a null handle.
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
                      "    C c1 = new(shared);\n"
                      "    C c2 = new(shared);\n"
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

}  // namespace
