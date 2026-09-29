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
                      "    static C c = new;\n"
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

// §15.3 (printed page 372) with §8.4 (printed pages 181-182) and §8.12
// (printed 188): a semaphore variable is a handle to the bucket, and a
// property made a handle to the module's semaphore by the constructor's
// `held = sem` refers to an object, so it compares unequal to null and is
// true in a condition, while `spare`, declared with no initializer, is null
// until `c.spare = new(2)` builds its bucket. probe() adds 1 for `held !=
// null`, 10 for `spare == null` and 100 for `if (held)`, the module 1000 for
// `c.held != null` and 10000 for `c.spare != null` after the new: 11111.
// The value under the property's name stayed 0 whatever the map held, so
// only `spare == null` read true, 10.
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

// §8.23 (printed pages 200-201) with §8.9 (printed 186): a nested class's
// method reaches the containing class's static semaphore by its bare name,
// so Inner's try_get(1) procures Outer's one key and the module's
// `Outer::s.try_get(1)` then finds none: 1 and 0 read as 10. Looked for
// along Inner's base chain alone, the bare name reached no bucket, so the
// nested take() procured nothing and the module's read 1: 01.
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

// The source of the static-initialization cases: the compilation unit
// declares `int keys = 1`, the typedef `head` and a class whose static
// semaphore property, declared through the type `type` names, is built by
// `new(keys)`; the module writes keys to 3 and then tries to procure one
// key twice, reading the two try_get() results as a two-digit number.
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

// §8.9 (printed page 186) with §6.21 (printed 132-133), §3.12.1 (printed
// 56) and §15.3.1 (printed 373): a static semaphore property's one bucket
// is created at the class's static initialization with the keys its
// `new(keys)` reads then, so the compilation unit's class holds the one key
// the unit's `int keys = 1` gives and the module's `keys = 3` before the
// first try_get() adds none: the first try_get(1) reads 1 and the second 0,
// 10. Built on the first reference instead, the `new` read the 3 and both
// reads were 1, 11.
TEST(SemaphoreSim, StaticSemaphorePropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticSemaphoreKeyedByUnitSrc("", "semaphore"), "r"),
            10u);
}

// §6.18 (printed page 118) with §8.9 (printed 186) and §6.21 (printed
// 132-133): a typedef name stands for its type, so a static property
// declared `static sem_t s = new(keys)` through the unit's `typedef
// semaphore sem_t` is the semaphore above, built at the class's static
// initialization with the one key keys then holds: 10 as above. The run's
// table of what a typedef stands for was filled after the unit's class was
// lowered, so the static initialization knew the property for no semaphore
// and the first `C::s.try_get(1)` built it, reading the 3, 11.
TEST(SemaphoreSim,
     StaticTypedefdSemaphorePropertyIsBuiltAtStaticInitialization) {
  EXPECT_EQ(RunAndGet(StaticSemaphoreKeyedByUnitSrc(
                          "typedef semaphore sem_t;\n", "sem_t"),
                      "r"),
            10u);
}

// §8.4 (printed pages 181-182) with §15.3 (printed 372) and §15.3.1
// (printed 373): a module's semaphore variable is a handle to the bucket
// new() returns, so one declared `semaphore unset;` with no initializer
// holds null, which comparing with null detects and a condition reads as
// false, one declared `semaphore filled = new(1);` refers to the bucket, and
// `unset = new(2)` in the initial block makes unset refer to one; `copy =
// filled` copies the handle and `filled = null` drops it. The reads add 1 for
// `unset == null`, 10 for `if (unset)`, 100 for `filled != null`, 1000 for `if
// (filled)`, 10000 for `unset != null` after the new, 100000 for `unset ==
// null` then, 1000000 for `copy != null` after the copy and 10000000 for
// `filled == null` after the null: 11011101. The variable's value stayed the
// 0 the declaration stored whether or not a new() had filled the bucket, so
// filled compared equal to null and unset stayed null after its new: 100001.
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

// §15.3.1 (printed page 373) with §8.4 (printed 182): the `bare = new(2)`
// that makes the handle refer to a bucket is the one that fills it, so the
// bucket gives two keys and refuses the third: try_get(1) reads 1, 1 and 0,
// and `bare != null` after the three adds 1000: 1110. The keys and the
// handle are read together, so a new() that filled the bucket and left the
// handle null reads 110, and one that marked the handle held and filled
// nothing 1000.
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

// §8.4 (printed page 182) with §15.3 (printed 372): equality and
// inequality compare two handles by the object each refers to, and each
// semaphore variable or property built by its own new() is a handle to its
// own bucket, so `first != second` on two module semaphores each built by
// `new(1)` is true, `third = first` makes third refer to first's bucket so
// `third == first` is true and `third == second` false, `o.p != o.q` on two
// properties each built by its own `new(1)` is true, and after `o.q = o.p`
// the two refer to one bucket so `o.p != o.q` is false. The reads add 1,
// 10, 100, 1000 and 10000 in that order: 1011. Every held handle carried
// the same 1, so first and second compared equal, o.p and o.q too, and
// third was told from second by nothing: 10110.
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

// §15.3 with §8.12: `b = a` leaves one bucket under both names, so the key
// b.put() returns lands in a's bucket, which then holds the two a.try_get(2)
// asks for, and `b = null` afterwards leaves a's bucket as it is: 1, then 1
// again after a.put(2), read as 11. b's name kept a bucket of its own, so the
// first a.try_get(2) found one key and answered 0.
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

// §15.3 with §25.3: an interface's semaphore is reached through the instance,
// `b.s`, whether it is built there by `b.s = new(1)` or by its declaration,
// and the bucket is the one the interface's own task waits on: the first
// try_get() takes the key and the second finds none, and grab() returns when
// `b.s.put()` returns the key at 3, read as 1, 0 and 3 in 103. Resolved by
// no key, every call through `b.s` reached no bucket and grab() never
// waited, 0 and 0.
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

// §15.3 with §23.6 and §27.4: a semaphore a loop generate block declares is
// reached from outside the block by the path through the instance,
// `g[1].s`, whose bucket holds the two keys its `new(i + 1)` gave: the first
// try_get(2) takes both and the second finds none, read as 10. The path
// reached no bucket, and both answered 0.
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

// §15.3.2 to §15.3.4 with §13.3 and §13.4: a call with no arguments may
// leave out its argument list, so `s.put;`, `r = s.try_get` and `s.get;` are
// the calls with the default key count of one: put returns a key, try_get
// takes it, and get waits for the put at 2, read as 1 and 2 in 12. Taken as
// member reads, none acted on the bucket, and get returned at 0: 0.
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

// §15.2 with §15.3.1 and §8.15: a class may extend the built-in semaphore, and
// `super.new(1)` fills the base's bucket with one key, which the inherited
// try_get(), called unqualified in a method, takes and then finds gone, and
// which `cs.put()` through the handle returns for `cs.try_get()` to take:
// 1, 0, 1 taken and 1, read as 1011. Built by nothing, every call answered 0.
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

// §15.3 with §7.8 and §7.10: a queue and an associative array of semaphores
// hold handles, so a method called on an element acts on the bucket that
// element refers to: q[0] and q[1], pushed from `t` rebuilt between, each
// hold their own keys, and m["a"] and m["b"] the ones their `new` gave.
// Read as the digits 1, 1, 0, 1, 1, 1, 0, 1: 11011101. The elements named no
// bucket, and every call answered 0.
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
