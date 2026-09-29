#include <gtest/gtest.h>

#include <string>

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
                      "    static C c = new;\n"
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
                      "    static C c = new;\n"
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

// §7.10 with §7.2 and §10.9.2: a pattern pushed into a queue of structures is
// packed member by member at each member's width, and `q[1].green` reads the
// member of the element; foreach over the queue reads each element's red. The
// pattern was concatenated at its elements' own widths and the member read
// as a name, both giving 0.
TEST(QueueSim, MembersOfPushedStructElements) {
  const char* src =
      "module t;\n"
      "  typedef struct { byte red, green, blue; } c_t;\n"
      "  c_t q[$];\n"
      "  int n, green, reds;\n"
      "  initial begin\n"
      "    q.push_back('{3, 5, 3});\n"
      "    q.push_back('{1, 10, 3});\n"
      "    q.push_front('{2, 20, 9});\n"
      "    n = q.size();\n"
      "    green = q[2].green;\n"
      "    reds = 0;\n"
      "    foreach (q[i]) reds = reds * 10 + q[i].red;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "green"), 10u);
  EXPECT_EQ(RunAndGet(src, "reds"), 231u);
}

// §7.10 with §6.16 and §8.5: a queue property of strings holds each element
// whole -- read in a method, through the handle, into a string variable, and
// returned by pop_front -- and not the four characters of a 32-bit value.
TEST(QueueSim, StringQueuePropertyKeepsWholeElements) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    string names[$];\n"
      "    function void fill(); names.push_back(\"hello\");\n"
      "      names.push_front(\"greetings\"); endfunction\n"
      "    function void show(); $display(\"%s\", names[1]); endfunction\n"
      "  endclass\n"
      "  C h; string s;\n"
      "  initial begin\n"
      "    h = new; h.fill(); h.show();\n"
      "    s = h.names[1];\n"
      "    $display(\"%s %0d %s\", h.names[0], s.len(), h.names.pop_front());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hello\ngreetings 5 greetings\n");
}

// §7.10 with §8.7 and §7.12: a queue property declared with an unpacked
// array concatenation holds its elements once the object is constructed, and
// a method reduces them and filters them by a with clause that reads another
// property, a local and a static property.
TEST(QueueSim, InitializedQueuePropertyReadInItsMethods) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int q[$] = {1, 5, 9, 12};\n"
      "    int threshold = 4;\n"
      "    static int limit = 8;\n"
      "    function int total(); return q.sum(); endfunction\n"
      "    function int above(); int lim = 10; int r[$], s[$], u[$];\n"
      "      r = q.find with (item > threshold);\n"
      "      s = q.find with (item > lim);\n"
      "      u = q.find with (item > limit);\n"
      "      return r.size() * 100 + s.size() * 10 + u.size(); endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%0d %0d %0d %0d\", h.q.size(), h.q[3], h.total(),\n"
      "             h.above());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 12 27 312\n");
}

// §7.10 with §8.4 and §7.12: a queue of a class type holds handles, so an
// element select, pop_front()'s result, q[$] and the item of a with clause
// each reach the object's property and method.
TEST(QueueSim, ElementsOfAQueueOfHandlesReachTheirObjects) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Item;\n"
      "    int id;\n"
      "    function new(int i); id = i; endfunction\n"
      "    function int twice(); return id * 2; endfunction\n"
      "  endclass\n"
      "  Item q[$], r[$];\n"
      "  Item it;\n"
      "  initial begin\n"
      "    it = new(8); q.push_back(it); it = new(1); q.push_back(it);\n"
      "    it = new(4); q.push_back(it);\n"
      "    $display(\"%0d %0d\", q[0].id, q[0].twice());\n"
      "    q.sort with (item.id);\n"
      "    r = q.find_first with (item.id == 4);\n"
      "    $display(\"%0d %0d %0d\", q[0].id, q[$].twice(), r[0].id);\n"
      "    $display(\"%0d %0d\", q.pop_front().id, q.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 16\n1 16 4\n1 2\n");
}

// §7.10 with §7.4 and §20.7: a queue's element type may be a fixed-size
// array, `int q[$][3]`. Each element pushed is a whole three-element array,
// so the queue's second dimension and the size of one element are 3, and
// `q[1][2]` is the third element of the second array pushed.
TEST(QueueSim, QueueOfFixedArraysHoldsWholeArrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$][3];\n"
      "  int row[3];\n"
      "  initial begin\n"
      "    q.push_back('{1, 2, 3});\n"
      "    q.push_back('{4, 5, 6});\n"
      "    $display(\"%0d %0d %0d %0d %0d\", $size(q), $size(q, 2), "
      "$size(q[1]),\n"
      "             q[1][2], q[0][0]);\n"
      "    q[0][1] = 9; row = q[0];\n"
      "    $display(\"%0d %0d %0d %0d\", row[0], row[1], row[2], q[1][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 3 3 6 1\n1 9 3 4\n");
}

// §7.10 and §7.8 with §25.3: a queue and an associative array declared in an
// interface are members of the instance, reached from the instantiating
// module through the instance's name like any other member: a push, an entry
// write, size(), num() and an element read through `i.` all act on the
// instance's own arrays.
TEST(QueueSim, QueueAndAssocArrayOfAnInterfaceInstance) {
  SimFixture f;
  auto out = RunCapture(
      "interface ifc;\n"
      "  int q[$];\n"
      "  int m[string];\n"
      "endinterface\n"
      "module t;\n"
      "  ifc i();\n"
      "  initial begin\n"
      "    i.q.push_back(5); i.q.push_back(8); i.m[\"a\"] = 1; i.m[\"b\"] = "
      "2;\n"
      "    #1 $display(\"%0d %0d %0d %0d %0d\", i.q.size(), i.m.num(), "
      "i.q[1],\n"
      "                i.m[\"b\"], i.m.exists(\"c\"));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 8 2 0\n");
}

// §7.10 with §7.4.2 and §20.7: the fixed-size array a queue's elements are
// may have any declared bounds. Under `int q[$][1:3]` an element's indices
// run 1 to 3 from the left, and under `int r[$][2:0]` 2 down to 0, so the
// leftmost value pushed is `q[0][1]` and `r[0][2]`.
TEST(QueueSim, QueueOfFixedArraysKeepsTheElementBounds) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$][1:3];\n"
      "  int r[$][2:0];\n"
      "  initial begin\n"
      "    q.push_back('{4, 5, 6}); r.push_back('{7, 8, 9});\n"
      "    q[0][2] = 50;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", $size(q, 2), $left(q, 2),\n"
      "             q[0][1], q[0][2], q[0][3]);\n"
      "    $display(\"%0d %0d %0d %0d\", $left(r, 2), r[0][2], r[0][1],\n"
      "             r[0][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 4 50 6\n2 7 8 9\n");
}

// §7.10 with §6.11: an element of a queue has the queue's element type however
// the value written into it was typed. On `bit [31:0] uq[$]`, `push_back(-5)`
// stores the unsigned 32'hFFFFFFFB, and on `int q[$]`, `push_back(u)` of the
// unsigned 32'hDEADBEEF stores a signed int, so of the two only `q[0]` is less
// than 0, as of a `bit [31:0]` and an `int` variable assigned the same values.
TEST(QueueSim, AnElementReadsWithTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  bit [31:0] uq[$];\n"
      "  int q[$];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    uq.push_back(-5); q.push_back(u);\n"
      "    $display(\"%0d %0d %0d\", uq[0] < 0, q[0] < 0, q[$] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n");
}

// §7.10 with §6.11 and §26.2: a queue a package declares has elements of its
// element type as a module's does, so on `int p::q[$]` the unsigned
// 32'hDEADBEEF pushed reads as a signed int, less than 0.
TEST(QueueSim, AnElementOfAPackageQueueReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  int q[$];\n"
      "endpackage\n"
      "module t;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    p::q.push_back(u);\n"
      "    $display(\"%0d\", p::q[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.10 with §6.11 and §13.5: a queue formal, `int a[$]`, has elements of its
// own element type, so the unsigned 32'hDEADBEEF the actual was given reads
// in the body as a signed int, less than 0.
TEST(QueueSim, AnElementOfAQueueFormalReadsWithTheFormalsType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$];\n"
      "  bit [31:0] u;\n"
      "  function int negative(int a[$]);\n"
      "    return a[0] < 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    q.push_back(u);\n"
      "    $display(\"%0d\", negative(q));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.10 with §6.11 and §7.4: each element of a fixed-size array of queues,
// `q_t fx[2]` under `typedef int q_t[$];`, is a queue of ints, so the unsigned
// 32'hDEADBEEF pushed onto `fx[1]` reads as a signed int, less than 0.
TEST(QueueSim, AnElementOfAFixedArrayOfQueuesReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  q_t fx[2];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    fx[1].push_back(u);\n"
      "    $display(\"%0d\", fx[1][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.10 with §6.11: each element of a queue of queues, `int qq[$][$]`, is a
// queue of ints, so the unsigned 32'hDEADBEEF pushed onto the queue that is
// pushed onto `qq` reads as a signed int, less than 0.
TEST(QueueSim, AnElementOfAQueueOfQueuesReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int qq[$][$];\n"
      "  int inner[$];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    inner.push_back(u);\n"
      "    qq.push_back(inner);\n"
      "    $display(\"%0d\", qq[0][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §7.10 with §6.11 and §7.8: each element of an associative array of queues,
// `int aq[string][$]`, is a queue of ints, whether a module or a block
// declares the array, so the unsigned 32'hDEADBEEF pushed onto `aq["k"]`
// reads as a signed int, less than 0.
TEST(QueueSim, AnElementOfAnAssociativeArrayOfQueuesReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aq[string][$];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    int bq[string][$];\n"
      "    u = 32'hDEADBEEF;\n"
      "    aq[\"k\"].push_back(u); bq[\"k\"].push_back(u);\n"
      "    $display(\"%0d %0d\", aq[\"k\"][0] < 0, bq[\"k\"][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(QueueSim, AnElementOfAnAssociativeArrayOfUnsignedQueuesReadsUnsigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  bit [31:0] aq[string][$];\n"
      "  initial begin\n"
      "    bit [31:0] bq[string][$];\n"
      "    aq[\"k\"].push_back(-5); bq[\"k\"].push_back(-5);\n"
      "    $display(\"%0d %0d\", aq[\"k\"][0] < 0, bq[\"k\"][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0\n");
}

}  // namespace
