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
  // The procure guard also governs the blocking get() path: a semaphore made
  // with a negative initial key count must block get() requests until enough
  // keys have been returned to satisfy the requested amount.
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
  // new()'s keyCount is the starting number of keys, not an upper bound: once
  // created, the bucket may hold more keys than were initially allocated.
  SemaphoreObject sem(3);
  EXPECT_EQ(sem.key_count, 3);
  sem.Put(4);
  EXPECT_EQ(sem.key_count, 7);
}

TEST(IpcSync, SemaphoreNewPositiveInitialKeysProcureImmediately) {
  // §15.3.1's procure guard has an accepting side: when new() establishes a
  // positive key count, get() and try_get() may procure keys straight away with
  // no intervening put(). This isolates the value supplied at construction —
  // not a later put() — as the sole source of the positive count, the accepting
  // complement to the negative-initial-value blocking cases above.
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

// §15.3.1 (printed page 373) with §26.3 (printed 808): a semaphore declared
// through a package's typedef reached by the package scope resolution
// operator, `p::sem_t s = new(2)` on `typedef semaphore sem_t`, is created
// with the two keys its new() names, as §6.18 has the typedef name stand for
// the semaphore. get(1) takes one, try_get(2) then finds one key short and
// answers 0, and try_get(1) takes the last and answers 1: r reads 1. The
// typedef was looked up by its bare name, which the table holds only under
// "p::sem_t", so no bucket was created: get(1) blocked and r stayed 0.
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

// §15.3.1 (printed page 373) with §8.7 (printed 184): a semaphore declared
// as a class property with `= new(2)` is built with two keys when the object
// is constructed, so the object's own task procures from the object's own
// bucket: get(1) takes one, try_get(2) then finds one key short and answers
// 0, and try_get(1) takes the last and answers 1, so r reads 1. The
// property's `new` was evaluated as a value and filled no bucket, and a
// bare `s` in a method was resolved through the run's tables, which hold no
// object's, so get(1) waited on nothing and r stayed 0.
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
                      "    C c = new;\n"
                      "    c.probe(y);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

// §8.4 (printed page 181) with §15.3.1 (printed 373): each object's
// properties are its own, so two objects of the class hold two buckets of
// one key each, and each object's try_get(1) procures its own object's key:
// 1 and 1 read as 11. One bucket shared by both would have given the second
// try_get() nothing, 10.
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
                      "    C c1 = new;\n"
                      "    C c2 = new;\n"
                      "    y = c1.take() * 10 + c2.take();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

// §8.11 with §15.3.2 (printed page 373): `this.s` inside a method names the
// running object's semaphore as the bare name does, and `c.s` from the
// module the object the handle refers to, so the two keys `this.s.put(2)`
// returns to a bucket built empty are what the module's `c.s.try_get(2)`
// procures, 1, and `c.s.try_get(1)` then finds the bucket empty, 0: 10.
// Neither receiver was taken by the semaphore paths, which took an
// identifier alone, so try_get() was served by no bucket.
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
                      "    C c = new;\n"
                      "    c.give();\n"
                      "    y = c.s.try_get(2) * 10 + c.s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §15.3.3 (printed page 373) with §15.3.1: a get() on the object's bucket
// waits where it stands until the keys are in the bucket, and the module's
// `c.s.put(1)` at time 5 is what puts them there, so the class task's get(1)
// completes at 5 and the branch that enabled it records 15 with the 10 it
// adds. A get() that did not wait would have recorded 10.
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

// §8.4 (printed page 181): a property declared `semaphore s;` with no
// initializer holds the null handle, and a method called through it is
// illegal, reported at the call as a method of a user class called through
// a null handle is. Resolved by name alone, the put() was served by no
// bucket and nothing was reported.
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
      "    C c = new;\n"
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

}  // namespace
