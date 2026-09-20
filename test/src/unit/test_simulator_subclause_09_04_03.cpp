#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSimulation, WaitConditionBlocks) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    #10 ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (ready) x = 8'd88;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(LevelSensitiveEventSimulation, WaitAlreadyTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait (1) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(LevelSensitiveEventSimulation, WaitStatementNullBody) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait(1) ;\n"
      "    x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

TEST(LevelSensitiveEventSimulation, WaitXConditionBlocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic cond;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cond = 1'bx;\n"
      "    x = 8'd0;\n"
      "    wait (cond) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveEventSimulation, WaitConditionWithDelayInBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 0;\n"
      "    b = 8'd55;\n"
      "    #5 enable = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(LevelSensitiveEventSimulation, WaitMultipleSignalCondition) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "    #5 a = 1;\n"
      "    #5 b = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (a && b) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

TEST(LevelSensitiveEventSimulation, WaitZeroConditionNeverUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (0) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

// A variable condition already satisfied when the wait is reached must let the
// following statement run without ever suspending the process.
TEST(LevelSensitiveEventSimulation, WaitVariableAlreadyTrueProceeds) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic flag;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    flag = 1;\n"
      "    x = 8'd0;\n"
      "    wait (flag) x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 200u);
}

// A multi-bit condition follows the same truthiness rule as a scalar: it is
// false while zero and becomes true once any bit is set, releasing the wait.
TEST(LevelSensitiveEventSimulation, WaitVectorNonzeroConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] cnt;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cnt = 4'd0;\n"
      "    x = 8'd0;\n"
      "    #5 cnt = 4'd6;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (cnt) x = 8'd123;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 123u);
}

// The clause requires that the statements *following* a wait remain blocked
// until the condition holds. With a null body, the observable is the next
// statement in the enclosing block. `tag` is latched to 77 one time step before
// `ready` rises, so a process that correctly suspends copies 77; one that ran
// at time 0 (never blocking) would have copied the initial 10. The distinct
// final value is what proves the following statement was actually held off.
TEST(LevelSensitiveEventSimulation, WaitNullBodyBlocksFollowingStatement) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] tag, x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    tag = 8'd10;\n"
      "    #5  tag = 8'd77;\n"
      "    #5  ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (ready) ;\n"
      "    x = tag;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

// The blocking branch of the clause's example: `enable` is 1 on entry, so
// wait(!enable) must suspend and only release once it clears. `b` is latched to
// 55 a time step before that release, so the delayed body `#10 a = b`
// copies 55. If the wait had failed to block, `a` would remain 0 because the
// condition is false at time 0. Complements WaitConditionWithDelayInBody, which
// exercises the already-true (no-block) branch of the same example.
TEST(LevelSensitiveEventSimulation, WaitBlocksThenDelayedBodyExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 1;\n"
      "    b = 8'd10;\n"
      "    #5  b = 8'd55;\n"
      "    #5  enable = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 55u);
}

// statement_or_null may be a begin-end block; after the wait releases, every
// statement in the block must run. `src` is latched to 9 one time step before
// `go` rises, so a correctly blocked process copies 9 into both members of the
// block (the second assignment reads the first), proving the whole block body
// executed post-release. A process that never blocked would have copied 1.
TEST(LevelSensitiveEventSimulation, WaitBlockBodyExecutesAfterUnblock) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic go;\n"
      "  logic [7:0] src, p, q;\n"
      "  initial begin\n"
      "    go = 0;\n"
      "    src = 8'd1;\n"
      "    #5  src = 8'd9;\n"
      "    #5  go = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    p = 8'd0;\n"
      "    q = 8'd0;\n"
      "    wait (go) begin\n"
      "      p = src;\n"
      "      q = p;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(val, 9u);
}

// The condition may be any integral expression, including a 2-state type. A
// zero `int` is false and blocks; once it becomes nonzero the wait releases and
// the following statement runs. This drives the §12.4 truth rule through a
// 2-state operand rather than the 4-state `logic` used by the other tests.
TEST(LevelSensitiveEventSimulation, WaitTwoStateIntConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  int count;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    x = 8'd0;\n"
      "    #5 count = 3;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (count) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §9.4.3: "the wait statement shall evaluate a condition; if it is false, the
// procedural statements following the wait statement shall remain blocked until
// that condition becomes true." Every case above writes its condition on a
// whole variable. This one writes it on a single bit, which is the operand
// whose collected name is BuildSelectPrefix's `v[1]` -- a position within a
// vector, which SimContext::FindVariable resolves to no object, so
// ExecWaitStatement armed no watcher and the condition was never re-tested.
//
// v starts all zero and x starts at 0, so a wait that never resumes leaves x
// at 0 rather than at 42, and only the bit the condition reads is set at time
// 10.
TEST(LevelSensitiveEventSimulation, WaitOnABitSelectResumesWhenThatBitChanges) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    x = 8'd0;\n"
      "    #10 v = 4'b0010;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (v[1]) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §9.4.3 states level-sensitive event control as an obligation about the truth
// of a condition rather than as a reaction to a change: "The wait statement
// shall evaluate a condition; and, if it is not true (as defined in 12.4), the
// procedural statements following the wait statement shall remain blocked
// until that condition becomes true before continuing." The clause draws the
// contrast itself -- the wait is "level-sensitive, as opposed to basic event
// control (specified by the @ character), which is edge-sensitive" -- so a
// §9.4.2 case does not stand in for this one: any route that observes the
// condition becoming true would satisfy §9.4.3. In this implementation,
// though, a wait parks on the same AnyChangeAwaiter that @ parks on and is
// released only by the written variable's watcher notification, so the two
// mechanisms fail together, which is what earns this clause its own case.
//
// The writer has to be a void function called with parentheses, because that
// is the only call form whose body runs through ExecFunctionBody and its
// identifier-assignment path. A task call is inlined onto the ordinary
// statement executor, which notifies already, so a task written here would
// pass whether or not the function path notifies and would prove nothing.
//
// `done` holds 8'd3 when the process parks and the wait's body writes 8'd91,
// neither of them a value a `logic [7:0]` reaches on its own, so a process
// left parked for the rest of the run reads back as 3 rather than 91.
TEST(LevelSensitiveEventSimulation, WaitResumesOnVoidFunctionWrite) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic gate;\n"
      "  logic [7:0] done;\n"
      "  function void open_gate;\n"
      "    gate = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    gate = 1'b0;\n"
      "    #5;\n"
      "    open_gate();\n"
      "  end\n"
      "  initial begin\n"
      "    done = 8'd3;\n"
      "    wait (gate) done = 8'd91;\n"
      "  end\n"
      "endmodule\n",
      f, "done");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 91u);
}

// §9.4.3 states level-sensitive event control as an obligation about the truth
// of a condition: "The wait statement shall evaluate a condition; and, if it is
// not true (as defined in 12.4), the procedural statements following the wait
// statement shall remain blocked until that condition becomes true before
// continuing." The clause names its own contrast -- the wait is
// "level-sensitive, as opposed to basic event control (specified by the @
// character), which is edge-sensitive" -- so a §9.4.2 case does not stand in
// for this one: any route that observed the condition becoming true would
// satisfy §9.4.3, and the clause asks for none in particular. In this
// implementation, though, ExecWait parks on the same AnyChangeAwaiter that @
// parks on, released only by the watcher notification of a variable the
// condition reads, so the level-sensitive and the edge-sensitive constructs
// fail together on one missing notification. That shared dependence is what
// earns this clause a case of its own rather than a §9.4.2 one standing in.
//
// The writer here is the increment operator in the ordinary body of a process:
// a bare `i++;` is a kExprStmt, which ExecStmt routes through
// ExecInlineTaskCall to EvalExpr and on to EvalIncDec, whose store to
// var->value said nothing to the variable's watchers. §11.4.2 makes these
// operators blocking assignments, so §9.4.2's "change in the value of the
// expression" covers an increment exactly as it covers an `=`, and a wait
// reading the incremented variable must be released by one.
//
// Three processes, so that the value the released statement copies is written
// by neither of the others at the moment it parks: `tag` holds 8'd12 when the
// waiter suspends and 8'd64 from time 5 onward, while `i` reaches 3 only at
// time 20. A waiter left parked for the rest of the run leaves `seen` at the
// 8'd3 it was given at time 0; one released too early would copy 8'd12; only a
// waiter released by the third increment reads 8'd64. None of the three is a
// value a `logic [7:0]` reaches on its own, whose default is 8'hxx.
TEST(LevelSensitiveEventSimulation, WaitResumesOnAnIncrementOperatorWrite) {
  auto val = RunAndGet(
      "module t;\n"
      "  int i;\n"
      "  logic [7:0] tag, seen;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    tag = 8'd12;\n"
      "  end\n"
      "  initial begin\n"
      "    #5  tag = 8'd64;\n"
      "    #5  i++;\n"
      "    #5  i++;\n"
      "    #5  i++;\n"
      "  end\n"
      "  initial begin\n"
      "    seen = 8'd3;\n"
      "    wait (i == 3) seen = tag;\n"
      "  end\n"
      "endmodule\n",
      "seen");
  EXPECT_EQ(val, 64u);
}

// §9.4.3 with §8.6 and §8.11: inside a class task the condition may read the
// object's own property, bare as `wait (go)`, as `wait (this.go)`, or in an
// expression `wait (n == 2)`, and the statement stays blocked until another
// process makes it true, here through a handle to the object. The property
// names resolve to no variable of the design, so the awaiter armed nothing
// and the three tasks never resumed, leaving the result at 0. Each task
// records the time it resumed: `go` is set at 4, `this.go` reads the same
// property, and `n` reaches 2 at 6, so the result is 4 * 100 + 4 * 10 + 6.
TEST(LevelSensitiveEventSimulation, WaitOnAnOwnPropertyInsideAClassTask) {
  auto val = RunAndGet(
      "class C;\n"
      "  bit go;\n"
      "  int n;\n"
      "  int woke_bare, woke_this, woke_expr;\n"
      "  task wait_bare();\n"
      "    wait (go) woke_bare = $time;\n"
      "  endtask\n"
      "  task wait_this();\n"
      "    wait (this.go) woke_this = $time;\n"
      "  endtask\n"
      "  task wait_expr();\n"
      "    wait (n == 2) woke_expr = $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    fork\n"
      "      h.wait_bare();\n"
      "      h.wait_this();\n"
      "      h.wait_expr();\n"
      "      begin\n"
      "        #3 h.n = 1;\n"
      "        #1 h.go = 1;\n"
      "        #2 h.n = 2;\n"
      "      end\n"
      "    join\n"
      "    result = h.woke_bare * 100 + h.woke_this * 10 + h.woke_expr;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 446u);
}

// §9.4.3 (printed page 236) with §7.10.2.1: the condition reads a declared
// queue through its size() method, and the wait stays blocked until a push
// from another process makes the size nonzero. CollectExprReads gives a call
// its arguments alone, so `q.size()` contributed nothing to the read set,
// ExecWait took the empty set for a condition nothing could change and
// returned at once: `q.pop_front()` on the still-empty queue read 0 at time 0,
// so `result` read 0. Released by the push at time 10, the pop reads 7 and
// the sum reads 7 * 100 + 10.
TEST(LevelSensitiveEventSimulation, WaitOnAQueueSizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (q.size() != 0);\n"
      "    v = q.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #10 q.push_back(7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 710u);
}

// §9.4.3 with §7.5.1 and §7.5.2 (printed page 158): a dynamic array's size()
// answers the size the last new[] gave it, so a wait on `d.size() == 3` is
// released by `d = new[3]` in another process. As for the queue above, the
// call contributed no read and the wait returned at once with the size still
// 0, leaving `result` at 0 * 100 + 0; released at time 20 it reads 3 * 100 +
// 20. The release also needs the new[] arm of TryQueueBlockingAssign
// (statement_assign_pattern.cpp) to announce the resize to the array's
// watchers, as every queue method announces its change.
TEST(LevelSensitiveEventSimulation,
     WaitOnADynamicArraySizeCallIsReleasedByNew) {
  auto val = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    wait (d.size() == 3);\n"
      "    result = d.size() * 100 + $time;\n"
      "  end\n"
      "  initial #20 d = new[3];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 320u);
}

// §9.4.3 with §8.5 and §8.11: inside a class task the condition reads the
// object's own queue property through size(), and a push through a handle
// from another process releases it. This is the shape of a blocking get on a
// queue-backed FIFO: the task is called from a forever loop, so a wait that
// returned at once spun at time 0, each pop reading 0 from the empty queue.
// The result records the value the first pop gave and the time it happened,
// 7 * 100 + 10, and the second pop the same for the push at 20, 9 * 100 + 20,
// where the spinning task left `first` at 0 and never reached the second.
TEST(LevelSensitiveEventSimulation,
     WaitOnAQueuePropertySizeCallInsideAClassTaskIsReleasedByAPush) {
  auto val = RunAndGet(
      "class H;\n"
      "  int m_queue[$];\n"
      "  int first, second;\n"
      "  task get(output int v);\n"
      "    wait (m_queue.size() != 0);\n"
      "    v = m_queue.pop_front();\n"
      "  endtask\n"
      "  task run();\n"
      "    int v;\n"
      "    forever begin\n"
      "      get(v);\n"
      "      if (first == 0) first = v * 100 + $time;\n"
      "      else second = v * 100 + $time;\n"
      "    end\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  H h = new;\n"
      "  int result;\n"
      "  initial h.run();\n"
      "  initial begin\n"
      "    #10 h.m_queue.push_back(7);\n"
      "    #10 h.m_queue.push_back(9);\n"
      "    #1 result = h.first * 10000 + h.second;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 7100920u);
}

// §9.4.3: a condition that is already true when the wait is reached blocks
// nothing, and the receiver's read added for the call above must not turn a
// true condition into a suspension. The queue holds 3 when the wait is
// evaluated, so the pop reads 3 at time 0 and `result` 3 * 100 + 0; a wait
// that parked until the push at time 10 would read 3 * 100 + 10.
TEST(LevelSensitiveEventSimulation, WaitOnANonEmptyQueueSizeCallDoesNotBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(3);\n"
      "    wait (q.size() != 0);\n"
      "    result = q.pop_front() * 100 + $time;\n"
      "  end\n"
      "  initial #10 q.push_back(9);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 300u);
}

// §9.4.3 (printed page 236) with §8.9 (printed 186): the condition reads a
// static queue property through the class scope operator, `C::all.size()`,
// and a push through the same name from another process releases it. A
// static property is the class's own storage, held by no object and named by
// no variable, so AnnounceQueueChange (eval_array_class_queue.cpp), given no
// owner and no declared queue's name, announced nothing and the wait, armed
// on the class's static watchers, stayed parked for ever: `result` read 0.
// Told to the class as a static value property's write is, the push at time
// 15 releases the wait, and the pop reads 4 * 100 + 15.
TEST(LevelSensitiveEventSimulation,
     WaitOnAStaticQueuePropertySizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "endclass\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (C::all.size() != 0);\n"
      "    v = C::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #15 C::all.push_back(4);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 415u);
}

// §9.4.3 with §8.9 and §8.10: inside a static task the condition names the
// static queue bare, `all.size()`, and a static function of the same class
// pushes to it bare from another process. Resolved to the class's queue but
// announced under the bare name, which no variable stands for, the push told
// nothing and the task stayed parked with `result` at 0; the wait returning
// at once instead would have popped 0 at time 0, reading 0 as well. Released
// by the push at time 20, the pop reads 9 * 100 + 20.
TEST(LevelSensitiveEventSimulation,
     WaitOnABareStaticQueueInAStaticTaskIsReleasedByAStaticFunctionsPush) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "  static int result;\n"
      "  static task get();\n"
      "    int v;\n"
      "    wait (all.size() != 0);\n"
      "    v = all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  endtask\n"
      "  static function void put(int x);\n"
      "    all.push_back(x);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial C::get();\n"
      "  initial #20 C::put(9);\n"
      "  initial #30 result = C::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 920u);
}

// §9.4.3 with §8.9 and §26.3: the class is declared in a package, and its
// static queue is named `p::C::all` from the module. The lowerer binds the
// class under `p::C`, which ScopeResolvedQueueProperty read as a class named
// by one identifier, so the queue was never found: the push pushed nothing,
// size() answered 0, and the wait, its condition collecting no static
// property, parked on nothing for ever with `result` at 0. Found through
// PackageQualifiedClassOf on both sides, the push at time 30 releases the
// wait and the pop reads 5 * 100 + 30.
TEST(LevelSensitiveEventSimulation,
     WaitOnAPackageClassStaticQueueSizeCallIsReleasedByAPush) {
  auto val = RunAndGet(
      "package p;\n"
      "  class C;\n"
      "    static int all[$];\n"
      "  endclass\n"
      "endpackage\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (p::C::all.size() != 0);\n"
      "    v = p::C::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #30 p::C::all.push_back(5);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 530u);
}

// §9.4.3 (printed page 236) with §8.13 (printed 189-190) and §8.9 (printed
// 186): the static property is C's, and D extends C, so `D::n` and `C::n`
// name one storage. The condition reads it as `D::n` and the release writes
// it as `D::n` from another process; the wait has to arm on C, the declaring
// class, which the write notifies. D's own static_properties hold D's
// declarations alone, so asked of them the wait armed nothing and stayed
// parked for ever: `result` read 0. Armed on the declaring class, the write
// at time 10 releases it and the read through `C::n` gives 2 * 100 + 10; the
// write of 1 at 5 shows the value, not the first write, releases it.
TEST(LevelSensitiveEventSimulation,
     WaitOnAnInheritedStaticPropertyThroughTheDerivedClassIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    wait (D::n == 2);\n"
      "    result = C::n * 100 + $time;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 D::n = 1;\n"
      "    #5 D::n = 2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 210u);
}

// §9.4.2 (printed page 232) with §8.13: an event control on `D::n` inside a
// module wakes on a write through `C::n`, the same storage. The operand
// resolved against D's own static_properties named no property, so the
// event control was skipped and the process waited for ever: `woke` read 0.
// Armed on C, the write of 5 at time 7 wakes it and the read gives 7 * 10 +
// 5.
TEST(LevelSensitiveEventSimulation,
     EventControlOnAnInheritedStaticPropertyWakesOnTheBaseClassWrite) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int woke;\n"
      "  initial @(D::n) woke = $time * 10 + C::n;\n"
      "  initial #7 C::n = 5;\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(val, 75u);
}

// §9.4.3 with §8.13 and §8.9: the static queue is C's and is named `D::all`
// on both sides. The push resolves the queue through the extends chain to
// C's storage and announces it to C's watchers, where the wait, asked of D's
// own static_properties, had armed nothing and stayed parked for ever with
// `result` at 0. Armed on the declaring class, the push at time 10 releases
// it and the pop reads 7 * 100 + 10.
TEST(LevelSensitiveEventSimulation,
     WaitOnAnInheritedStaticQueueSizeCallIsReleasedByAPushThroughTheDerived) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "endclass\n"
      "class D extends C;\n"
      "endclass\n"
      "module t;\n"
      "  int v, result;\n"
      "  initial begin\n"
      "    wait (D::all.size() != 0);\n"
      "    v = D::all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  end\n"
      "  initial #10 D::all.push_back(7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 710u);
}

// §9.4.3 with §8.13 and §8.10: inside a static task of D the condition names
// the inherited static queue bare, `all.size()`, and a static function of C
// pushes to it bare. The bare name resolves through the running method's
// class, D, whose own static_properties hold no `all`, so the wait armed
// nothing and the task stayed parked with `result` at 0. Resolved to the
// declaring class C on both sides, the push at time 25 releases it and the
// pop reads 6 * 100 + 25.
TEST(LevelSensitiveEventSimulation,
     WaitOnABareInheritedStaticQueueInADerivedStaticTaskIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int all[$];\n"
      "  static function void put(int x);\n"
      "    all.push_back(x);\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  static int result;\n"
      "  static task get();\n"
      "    int v;\n"
      "    wait (all.size() != 0);\n"
      "    v = all.pop_front();\n"
      "    result = v * 100 + $time;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial D::get();\n"
      "  initial #25 C::put(6);\n"
      "  initial #40 result = D::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 625u);
}

// §9.4.3 with §8.13 and §8.10: inside a static task of D the condition names
// the inherited static value property bare, `n == 3`, and a static function
// of D writes it bare. Both resolve through D to C's one storage, and the
// write notifies C, where the wait is armed; asked of D's own
// static_properties, the wait armed nothing and stayed parked with `result`
// at 0. Released by the write at time 30, the read gives 3 * 100 + 30; the
// write of 1 at 15 shows the value releases it.
TEST(LevelSensitiveEventSimulation,
     WaitOnABareInheritedStaticPropertyInADerivedStaticTaskIsReleased) {
  auto val = RunAndGet(
      "class C;\n"
      "  static int n;\n"
      "endclass\n"
      "class D extends C;\n"
      "  static int result;\n"
      "  static task get();\n"
      "    wait (n == 3);\n"
      "    result = n * 100 + $time;\n"
      "  endtask\n"
      "  static function void set(int x);\n"
      "    n = x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial D::get();\n"
      "  initial begin\n"
      "    #15 D::set(1);\n"
      "    #15 D::set(3);\n"
      "  end\n"
      "  initial #40 result = D::result;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 330u);
}

}  // namespace
