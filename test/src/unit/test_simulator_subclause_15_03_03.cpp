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

// §15.3.3: a get() with more keys required than available blocks until the
// keys become available; the process then runs. Two processes block on an
// empty bucket; each put() of one key releases the head of the queue in turn.
TEST(IpcSync, SemaphoreGetBlocksThenRunsInArrivalOrder) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto first = SpawnGetter(sem, 1, ran, 1);
  auto second = SpawnGetter(sem, 1, ran, 2);
  first.h.resume();   // arrives first, blocks
  second.h.resume();  // arrives second, blocks
  ASSERT_EQ(sem.waiters.size(), 2u);
  EXPECT_TRUE(ran.empty());

  sem.Put(1);  // releases the earliest arrival
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);

  sem.Put(1);  // releases the next
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);

  first.h.destroy();
  second.h.destroy();
}

// §15.3.3: the waiting queue is FIFO and arrival order shall be preserved. The
// earliest arrival requires two keys; a process that arrived later requiring a
// single key must not be served ahead of it. A lone key satisfies neither, and
// once two keys are available the head runs first, then the later arrival.
TEST(IpcSync, SemaphoreGetFifoPreservesArrivalOrderUnderHeadOfLine) {
  SemaphoreObject sem(0);
  std::vector<int> ran;
  auto head = SpawnGetter(sem, 2, ran, 1);   // first in, needs 2
  auto later = SpawnGetter(sem, 1, ran, 2);  // second in, needs 1
  head.h.resume();
  later.h.resume();
  ASSERT_EQ(sem.waiters.size(), 2u);

  sem.Put(1);  // one key available, but head needs 2; FIFO holds the later,
               // single-key request behind it rather than letting it jump ahead
  EXPECT_TRUE(ran.empty());
  EXPECT_EQ(sem.key_count, 1);

  sem.Put(1);  // bucket reaches 2 — the head runs and consumes both keys
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_EQ(sem.key_count, 0);
  ASSERT_EQ(sem.waiters.size(), 1u);

  sem.Put(1);  // the later arrival is served next
  ASSERT_EQ(ran.size(), 2u);
  EXPECT_EQ(ran[1], 2);
  EXPECT_TRUE(sem.waiters.empty());

  head.h.destroy();
  later.h.destroy();
}

// §15.3.3: when the required key count is at most the number available, get()
// reduces the bucket, the method returns, and execution continues. Observed
// through the task path: a process spawned against a bucket that already holds
// enough keys acquires them on its first resume without ever parking on the
// waiter queue, and its body runs straight through.
TEST(IpcSync, SemaphoreGetImmediateAcquireContinuesWithoutBlocking) {
  SemaphoreObject sem(5);
  std::vector<int> ran;
  auto getter = SpawnGetter(sem, 3, ran, 1);
  getter.h.resume();  // keys available: acquires without suspending, body runs
  ASSERT_EQ(ran.size(), 1u);
  EXPECT_EQ(ran[0], 1);
  EXPECT_TRUE(sem.waiters.empty());
  EXPECT_EQ(sem.key_count, 2);

  getter.h.destroy();
}

// §15.3.3 with §9.7 and §8.11: a class task that waits in get() goes on, once
// the put() from another process frees the keys, as the process and on the
// object that called it, so `got` is written on w and reads 7 and the time 4,
// giving 71. Resumed under the process that called put(), the task read
// `this.id` of no object and wrote `got` nowhere.
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

// §15.3.3 (printed page 373): a negative key count handed to get() is an
// error, reported at the call, and the process does not wait for keys that
// could never satisfy it: the empty bucket leaves r written at time 0, 5.
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

// §15.4.3, §15.4.5, §15.4.7 and §15.3.3 with §8.6 and §11.3.1: a call
// statement that may wait -- a mailbox's put(), peek() and get(), a
// semaphore's get() -- through a property of a call's result runs the call
// once, as the statement resolves the object it waits on, and acts on that
// object: 5 is put, peeked into y and taken into x, and both keys are taken.
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
