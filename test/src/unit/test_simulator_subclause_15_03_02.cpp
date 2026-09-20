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

// §15.3.2: a process suspended waiting for keys shall execute once put() has
// returned enough keys — and not before. The getter parks needing 3 keys; a
// put() of 2 is insufficient and leaves it suspended, while the put() that
// brings the bucket to 3 resumes it.
TEST(IpcSync, SemaphorePutWakesSuspendedWaiterWhenEnoughReturned) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto getter = SpawnGetter(sem, 3, ran, 1);
  getter.h.resume();  // runs to the co_await, blocks needing 3 keys
  ASSERT_EQ(sem.waiters.size(), 1u);
  EXPECT_TRUE(ran.empty());

  sem.Put(2);  // not enough — stays suspended
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.waiters.size(), 1u);
  EXPECT_EQ(sem.key_count, 2);

  sem.Put(1);  // bucket reaches 3 — the suspended process executes
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  getter.h.destroy();
}

// §15.3.2: the wake rule fires per put(), not per key. A single put() that
// returns enough keys for more than one suspended process shall resume every
// waiter it can satisfy — here two processes (needing 1 and 2 keys) both
// parked, and one put(3) is enough for both, so both execute in arrival order
// off that single return rather than requiring a separate put() apiece.
TEST(IpcSync, SemaphorePutSingleReturnWakesMultipleWaiters) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 2, ran, 2);
  first.h.resume();   // arrives first, needs 1, blocks
  second.h.resume();  // arrives second, needs 2, blocks
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(3);  // one return, enough for both — both processes execute
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 0);

  first.h.destroy();
  second.h.destroy();
}

// §15.3.2 (printed page 373): put() returns its keys where it stands, so a
// void function's put(1) on a bucket built empty leaves one key: the
// module's first try_get(1) procures it and the second finds none, 10. A
// function's put() is served by the expression evaluator as a process's is,
// and this pins that beside the get() below.
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

// §15.3.3 (printed page 373): get() takes the keys at once when the bucket
// holds enough, and §13.4 (printed 340) has a function return without
// suspending its process, so a void function's get(1) on new(2) leaves one
// key: the module's try_get(2) fails and its try_get(1) succeeds, 1. Served
// by the expression evaluator, which answers put() and try_get() alone, the
// function's get(1) took nothing and the two keys read 10.
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

// §15.3.3 with §15.3.2: a function's get(2) on new(2) empties the bucket,
// so the module's try_get(1) reads 0 until its put(1) returns a key, after
// which try_get(1) reads 1: 2 + 0 * 10 + 1, 3. A get() that took nothing
// would have read 13.
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

// §13.4 (printed page 340) with §15.3.3 (printed 373): a get(3) on a bucket
// holding 2 keys would suspend the process, which a function may not do, so
// the function's get(3) is the error, reported at the call under §13.4 with
// the bucket as it was: the module's try_get(2) procures both keys, 1. A
// get() that took the two keys anyway would have read 0.
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

// §8.7 with §15.3.1 (printed page 373) and §15.3.3: a semaphore declared as
// a class property is the object's own, so a method's bare `s.get(1)` in a
// function body takes the key from that object's bucket: the module's
// `c.s.try_get(1)` then finds none, 5. Resolved by name alone the get()
// reached no bucket and the key was still there, 15.
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
                      "    C c = new;\n"
                      "    c.take();\n"
                      "    y = c.s.try_get(1) * 10 + 5;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

}  // namespace
