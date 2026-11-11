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

TEST(QueueSim, AnElementOfABlockAssociativeArrayOfTypedefQueuesReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    q_t all[string];\n"
      "    u = 32'hDEADBEEF;\n"
      "    all[\"k\"].push_back(u);\n"
      "    $display(\"%0d\", all[\"k\"][0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(QueueSim, AnEmptyConcatenationEmptiesAQueueOfArrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][3];\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r.push_back('{1, 2, 3});\n"
      "    r = {};\n"
      "    $display(\"%0d\", r.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(QueueSim, AssigningAQueueOfArraysCopiesEveryElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][3], s[$][3];\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r.push_back('{1, 2, 3});\n"
      "    s = r;\n"
      "    r[0][1] = 9;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", s.size(), s[0][0], s[0][1],\n"
      "             s[1][2], r[0][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 5 3 9\n");
}

TEST(QueueSim, AQueueNestedThreeDeepHoldsANestedPattern) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int a[$][$][$], b[$][$][$];\n"
      "  initial begin\n"
      "    a = '{'{'{1, 2}, '{3}}, '{'{4}}};\n"
      "    b = a;\n"
      "    a[0][0][1] = 7;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", a.size(), a[0].size(),\n"
      "             a[0][0][1], a[1][0][0], b[0][0][1], b[0][1][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 7 4 2 3\n");
}

TEST(QueueSim, AQueueOfTwoDimensionalArraysHoldsItsElements) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][2][2], s[$][2][2];\n"
      "  initial begin\n"
      "    r.push_back('{'{9, 8}, '{7, 6}});\n"
      "    r[0][1][1] = 5;\n"
      "    r.push_back('{'{1, 2}, '{3, 4}});\n"
      "    s = r;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", r.size(), r[0][1][0],\n"
      "             r[0][0][1], r[0][1][1], s[1][0][1], s[1][1][0]);\n"
      "    r = '{'{'{0, 0}, '{0, 1}}};\n"
      "    $display(\"%0d %0d\", r.size(), r[0][1][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 7 8 5 2 3\n1 1\n");
}

TEST(QueueSim, ABlockQueueOfArraysHoldsItsElements) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    int q[$][3];\n"
      "    int r[$][2][2];\n"
      "    int d[][1:2];\n"
      "    q.push_back('{1, 2, 3});\n"
      "    r.push_back('{'{9, 8}, '{7, 6}});\n"
      "    d = new[2];\n"
      "    d[1][2] = 5;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", q[0][2], r.size(), r[0][1][0],\n"
      "             d[1][2], d[0].size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 7 5 2\n");
}

TEST(QueueAccess, DISABLED_QueueOfTypedefArraysPushesInsertsAndPops) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef int a_t [2];\n"
                 "  a_t q [$]; a_t b = '{1, 2}, c = '{3, 4}, d = '{5, 6}, "
                 "r;\n"
                 "  initial begin\n"
                 "    q.push_back(b); q.push_front(c); q.insert(1, d);\n"
                 "    $display(\"%0d %0d %0d %0d\", q.size(), q[0][0], "
                 "q[1][1], q[2][0]);\n"
                 "    r = q.pop_front(); $display(\"%0d %0d\", r[0], "
                 "r[1]);\n"
                 "    r = q.pop_back(); $display(\"%0d %0d\", r[0], "
                 "r[1]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "3 3 6 1\n3 4\n1 2\n");
}

TEST(QueueAccess, DISABLED_QueueOfArraysPopsWholeArrays) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int q [$][2]; int b [2] = '{1, 2}, c [2] = '{3, 4}, "
                       "r [2];\n"
                       "  initial begin\n"
                       "    q.push_back(b); q.push_front(c);\n"
                       "    r = q.pop_front(); $display(\"%0d %0d\", r[0], "
                       "r[1]);\n"
                       "    r = q.pop_back(); $display(\"%0d %0d %0d\", r[0], "
                       "r[1], q.size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 4\n1 2 0\n");
}

TEST(QueueAccess, DISABLED_QueueOfTypedefArraysFromAConcatenation) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef int a_t [2];\n"
                       "  a_t q [$]; a_t b = '{1, 2}, c = '{3, 4};\n"
                       "  initial begin\n"
                       "    q = {b, c};\n"
                       "    $display(\"%0d %0d %0d\", q.size(), q[0][1], "
                       "q[1][0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 2 3\n");
}

TEST(QueueAccess, QueuesOfStructuresAndUnionsPushAndPop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int x; byte y;} s_t;\n"
                       "  typedef union {int i; bit [31:0] b;} u_t;\n"
                       "  s_t sq [$]; s_t sv; u_t uq [$]; u_t uv;\n"
                       "  initial begin\n"
                       "    sv.x = 7; sv.y = 8; sq.push_back(sv); sv.x = 1;\n"
                       "    sq.push_front(sv); sv = sq.pop_back();\n"
                       "    $display(\"%0d %0d %0d\", sv.x, sv.y, sq[0].x);\n"
                       "    uv.i = 9; uq.push_back(uv); uv = uq.pop_front();\n"
                       "    $display(\"%0d %0d\", uv.i, uq.size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 8 1\n9 0\n");
}

TEST(QueueAccess, ClauseDeclarationsAndQueueOperatorRules) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  byte q1 [$]; string names [$] = {\"Bob\"};\n"
          "  integer Q [$] = {3, 2, 7}; bit q2 [$:255];\n"
          "  int A [$] = {10, 20, 30, 40}; int R [$]; int a, b; integer xi;\n"
          "  initial begin\n"
          "    $display(\"%0d %0d %0d %0d\", q1.size(), names.size(), Q[2], "
          "q2.size());\n"
          "    a = 2; b = 1; R = A[a:b]; $display(\"%0d\", R.size());\n"
          "    R = A[1:1]; $display(\"%0d %0d\", R.size(), R[0]);\n"
          "    R = A[5:5]; $display(\"%0d\", R.size());\n"
          "    R = A[-1:-1]; $display(\"%0d\", R.size());\n"
          "    xi = 'x; R = A[1:xi]; $display(\"%0d\", R.size());\n"
          "    xi = 'z; R = A[xi:2]; $display(\"%0d\", R.size());\n"
          "    R = A[-2:1]; $display(\"%0d %0d\", R.size(), R[0]);\n"
          "    R = A[2:9]; $display(\"%0d %0d\", R.size(), R[$]);\n"
          "    a = 0; b = 3; R = A[a+1:b]; $display(\"%0d\", R.size());\n"
          "  end\n"
          "endmodule\n",
          f),
      "0 1 7 0\n0\n1 20\n0\n0\n0\n0\n2 10\n2 40\n3\n");
}

}  // namespace
