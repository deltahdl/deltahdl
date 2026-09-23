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

// §7.10 with §7.4: a queue's elements may themselves be queues, and a method
// called on one, `qq[1].push_back(42)`, operates on that element. Pushed a
// queue of two and an empty one, the outer queue holds two elements, the
// first of size 2 and the second, after its push, of size 1 holding 42.
// With no storage for the inner queues, every inner size read 0 and the
// element 0.
TEST(QueueAccess, ElementOfAQueueOfQueuesTakesAPush) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int qq[$][$];\n"
                      "  int inner[$];\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    inner.push_back(1);\n"
                      "    inner.push_back(2);\n"
                      "    qq.push_back(inner);\n"
                      "    qq.push_back({});\n"
                      "    qq[1].push_back(42);\n"
                      "    out = qq.size() * 100000 + qq[0].size() * 10000 +\n"
                      "          qq[1].size() * 1000 + qq[1][0];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            221042u);
}

// §7.10 with §7.8.7: an element of an associative array of queues is
// allocated when a queue method first uses it, so three pushes into
// aq["a"] and aq["b"] leave two entries of sizes 2 and 1, aq["a"] holding 3
// then 4, and pop_front on it answers 3 and leaves one element. Treated as a
// read of a missing entry, each push warned and stored nothing, and every
// count read 0.
TEST(QueueAccess, AssociativeEntryIsAllocatedByAQueueMethod) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int aq[string][$];\n"
                "  int out;\n"
                "  initial begin\n"
                "    aq[\"a\"].push_back(3);\n"
                "    aq[\"a\"].push_back(4);\n"
                "    aq[\"b\"].push_back(9);\n"
                "    out = aq.num() * 1000000 + aq[\"a\"].size() * 100000"
                " +\n"
                "          aq[\"b\"].size() * 10000 + aq[\"a\"][0] * 1000 "
                "+\n"
                "          aq[\"a\"][1] * 100;\n"
                "    out = out + aq[\"a\"].pop_front() * 10;\n"
                "    out = out + aq[\"a\"].size();\n"
                "  end\n"
                "endmodule\n",
                "out"),
      2213431u);
}

// The same for a fixed-size and a dynamic array whose element type is a
// typedef'd queue: fx[1] and dy[1] each take one push and hold it.
TEST(QueueAccess, ElementsOfFixedAndDynamicArraysOfQueuesTakePushes) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef int q_t[$];\n"
                      "  q_t fx[2];\n"
                      "  q_t dy[];\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    dy = new[2];\n"
                      "    fx[1].push_back(4);\n"
                      "    dy[1].push_back(5);\n"
                      "    out = fx[1].size() * 1000 + dy[1].size() * 100 +\n"
                      "          fx[1][0] * 10 + dy[1][0];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            1145u);
}

// UVM's uvm_resource_pool::sort_by_precedence buckets resources by pushing
// onto `all[prec]` of a function-local `rsrc_sv_q_t all[int]`: push_front on
// an entry allocates it and prepends, so all[2] holds 6 then 5 and all[7]
// holds 8, two entries in all.
TEST(QueueAccess, PushFrontOnATypedefQueueEntryOfALocalAssociativeArray) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef int q_t[$];\n"
                      "  int out;\n"
                      "  function automatic int bucket();\n"
                      "    q_t all[int];\n"
                      "    all[2].push_front(5);\n"
                      "    all[2].push_front(6);\n"
                      "    all[7].push_front(8);\n"
                      "    return all.num() * 1000 + all[2].size() * 100 +\n"
                      "           all[2][0] * 10 + all[7][0];\n"
                      "  endfunction\n"
                      "  initial out = bucket();\n"
                      "endmodule\n",
                      "out"),
            2268u);
}

// §10.10 with §7.10: an element of an array of queues is an unpacked array,
// so as an item of an unpacked array concatenation it contributes its
// elements -- UVM's sort_by_precedence_q rebuilds its queue as `q = {q,
// all[iter]}` over a local `rsrc_sv_q_t all[int]`, the typedef a class's
// queue of handles. Bucketed as 7 under key 1 and 5 then 6 under key 2, the
// rebuilt queue holds three handles whose ids read 756; taken as the entries'
// placeholders, it held two values that were no handles.
TEST(QueueAccess, ElementQueueOfAClassScopeTypedefIsAConcatenationItem) {
  EXPECT_EQ(RunAndGet("class B;\n"
                      "  int id;\n"
                      "  function new(int i); id = i; endfunction\n"
                      "endclass\n"
                      "class H;\n"
                      "  typedef B bq_t[$];\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  function automatic int rebuild();\n"
                      "    H::bq_t all[int];\n"
                      "    B q[$];\n"
                      "    B b;\n"
                      "    b = new(5);\n"
                      "    all[2].push_back(b);\n"
                      "    b = new(6);\n"
                      "    all[2].push_back(b);\n"
                      "    b = new(7);\n"
                      "    all[1].push_back(b);\n"
                      "    foreach (all[k]) q = {q, all[k]};\n"
                      "    return q.size() * 1000 + q[0].id * 100 + q[1].id * "
                      "10 +\n"
                      "           q[2].id;\n"
                      "  endfunction\n"
                      "  initial out = rebuild();\n"
                      "endmodule\n",
                      "out"),
            3756u);
}

}  // namespace
