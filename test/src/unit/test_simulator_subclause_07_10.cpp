#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueAccess, DefaultInitializationIsEmpty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Cross-link with §10.10: §7.10 promises that the empty unpacked array
// concatenation `{}` denotes the empty queue. The same TryQueueBlockingAssign
// path that satisfies §10.10's zero-item rule must drain a previously
// populated queue down to zero elements here.
TEST(QueueAccess, EmptyConcatProducesEmptyQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{5, 6, 7};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Each queue element is named by its ordinal position: index 0 is the first
// element, index `$` is the last. With a three-element queue this becomes
// q[0] == 10 and q[$] == 30, which exercises the simulator's $-as-last-index
// binding in EvalQueueIndex.
TEST(QueueAccess, ZeroIndexIsFirstAndDollarIsLast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  int first;\n"
      "  int last;\n"
      "  initial begin\n"
      "    first = q[0];\n"
      "    last = q[$];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* first = f.ctx.FindVariable("first");
  auto* last = f.ctx.FindVariable("last");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 10u);
  EXPECT_EQ(last->value.ToUint64(), 30u);
}

// §7.10.1: "Queues shall support the same operations that can be performed on
// fixed-size unpacked arrays", and §9.4.2 puts the duty of announcing an
// aggregate element's change on the writer -- "Changing the value of object
// data members, aggregate elements, or the size of a dynamically sized array
// referenced by a method or function shall cause the event expression to be
// reevaluated". A queue's elements live outside the variable registered under
// its name, so the indexed write has to notify that variable's watchers the way
// every mutating method does. 99 against 20 is the discriminating pair: 20 is
// the value a run that notified on push_back and not on the indexed write
// leaves standing, so no partial fix reads it.
TEST(QueueAccess, IndexedElementWriteWakesAnAlwaysCombThatReadsTheElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int b;\n"
      "  always_comb b = q[1];\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    #1 q[1] = 99;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// The other route onto the same notification, and the case the awaiter's own
// comment names in prose: a wait re-evaluates its whole condition on each
// notification where an always_comb re-runs its body, so a fix could serve one
// and not the other.
TEST(QueueAccess, IndexedElementWriteWakesAWaitOnTheElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int woke;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    wait (q[0] == 3);\n"
      "    woke = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    #1 q[0] = 3;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §7.10.1 makes `q[$+1]` a legal write and §7.10 has the queue resize itself to
// take it, so this store changes the element and the size at once -- both of
// them changes §9.4.2 names. It is the append branch rather than the in-range
// one, a separate store in the same function, so a notification placed only on
// the latter leaves it reading 0.
TEST(QueueAccess, IndexedAppendWakesAnAlwaysCombThatReadsTheQueue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int b;\n"
      "  always_comb b = q[0];\n"
      "  initial begin\n"
      "    #1 q[0] = 7;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §7.10 with §8.5: a queue property declared with an initializer holds the
// initializer's elements once the object is constructed (§8.7), and a
// whole-queue assignment in a method, `q = {q, x}` (§10.10), appends to it:
// three elements, the first still 5 and the last the appended 7.
TEST(QueueAccess, QueuePropertyInitializerAndWholeQueueAssignmentInAMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$] = {5, 6};\n"
                      "  function void grow(int x);\n"
                      "    q = {q, x};\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.grow(7);\n"
                      "    out = c.q.size() * 100 + c.q[0] * 10 + c.q[$];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            357u);
}

// §7.10: a whole-queue assignment through a handle from the module, written
// as an assignment pattern (§10.9), replaces the property's elements, and the
// empty concatenation `{}` empties it.
TEST(QueueAccess, QueuePropertyAssignedThroughAHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$];\n"
                      "  function int count();\n"
                      "    return q.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    c.q = '{3, 4, 5};\n"
                      "    out = c.count() * 100 + c.q[2] * 10;\n"
                      "    c.q = {};\n"
                      "    out = out + c.count() + 1;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            351u);
}

}  // namespace
