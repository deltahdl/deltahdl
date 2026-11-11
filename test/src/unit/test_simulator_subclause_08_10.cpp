#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StaticMethodSimulation, StaticMethodCallableWithoutAnyInstance) {
  EXPECT_EQ(RunAndGet("class Util;\n"
                      "  static function int add(int a, int b);\n"
                      "    return a + b;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = Util::add(30, 12);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(StaticMethodSimulation, StaticMethodReadsInlineInitializedStaticProperty) {
  EXPECT_EQ(RunAndGet("class id;\n"
                      "  static int current = 100;\n"
                      "  static function int next_id();\n"
                      "    return current;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = id::next_id();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            100u);
}

TEST(StaticMethodSimulation, StaticTaskModifiesStaticProperty) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "  static task bump();\n"
                      "    count = count + 5;\n"
                      "  endtask\n"
                      "  static function int get();\n"
                      "    return count;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter::bump();\n"
                      "    Counter::bump();\n"
                      "    result = Counter::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(StaticMethodSimulation, StaticMethodModifiesStaticProperty) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "  static function void inc();\n"
                      "    count = count + 1;\n"
                      "  endfunction\n"
                      "  static function int get();\n"
                      "    return count;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter::inc();\n"
                      "    Counter::inc();\n"
                      "    Counter::inc();\n"
                      "    result = Counter::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(StaticMethodSimulation, StaticMethodCallsStaticMethod) {
  EXPECT_EQ(RunAndGet("class Math;\n"
                      "  static function int double_it(int x);\n"
                      "    return x + x;\n"
                      "  endfunction\n"
                      "  static function int quad(int x);\n"
                      "    return double_it(double_it(x));\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = Math::quad(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(StaticMethodSimulation, StaticMethodSharedAcrossInstances) {
  EXPECT_EQ(RunAndGet("class Id;\n"
                      "  static int current;\n"
                      "  static function int next_id();\n"
                      "    current = current + 1;\n"
                      "    return current;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Id a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.next_id();\n"
                      "    b.next_id();\n"
                      "    result = Id::next_id();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(StaticMethodSimulation, AbstractPackageClassStaticMethodCalledByBareName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  virtual class base_t;\n"
                      "    static function int get();\n"
                      "      return 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = base_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(StaticMethodSimulation, PackageClassStaticMethodSharesOneStaticProperty) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class cnt_t;\n"
                      "    static int total = 30;\n"
                      "    static function int bump();\n"
                      "      total = total + 4;\n"
                      "      return total;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    void'(cnt_t::bump());\n"
                      "    result = p::cnt_t::bump();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            38u);
}

TEST(StaticMethodSimulation, StaticTaskWithADelayConsumesTime) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int s;\n"
                      "  static int at;\n"
                      "  static task run();\n"
                      "    #3 s = s + 6;\n"
                      "    at = at + $time;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  Counter h;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    Counter::run();\n"
                      "    h.run();\n"
                      "    result = Counter::at * 10 + Counter::s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            102u);
}

TEST(StaticMethodSimulation, StaticTaskForksAndJoins) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "  static int seen;\n"
                      "  static task run();\n"
                      "    int loc;\n"
                      "    fork\n"
                      "      #3 s = 6;\n"
                      "      #1 loc = 9;\n"
                      "    join\n"
                      "    seen = s * 1000 + loc * 10 + $time;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::run();\n"
                      "    result = C::seen;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            6093u);
}

TEST(StaticMethodSimulation, ForkOfAStaticMethodCalledFromAnObjectHasNoThis) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class E;\n"
      "  int v;\n"
      "endclass\n"
      "class C;\n"
      "  local static E pool[$];\n"
      "  static function void later();\n"
      "    fork\n"
      "      begin\n"
      "        E e = new;\n"
      "        #1;\n"
      "        pool.push_back(e);\n"
      "      end\n"
      "    join_none\n"
      "  endfunction\n"
      "  static task hold();\n"
      "    fork\n"
      "      begin\n"
      "        E e = new;\n"
      "        #1;\n"
      "        pool.push_back(e);\n"
      "      end\n"
      "    join_none\n"
      "  endtask\n"
      "  static function int n();\n"
      "    return pool.size();\n"
      "  endfunction\n"
      "endclass\n"
      "class R;\n"
      "  int x;\n"
      "  function void start();\n"
      "    C::later();\n"
      "  endfunction\n"
      "  task begin_hold();\n"
      "    C::hold();\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static R r = new;\n"
      "    r.start();\n"
      "    r.begin_hold();\n"
      "    #2 result = C::n();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StaticMethodSimulation,
     PackageClassMethodStaticLocalSharedByEveryInstance) {
  auto val = RunAndGet(
      "package p;\n"
      "  class C;\n"
      "    static function int count();\n"
      "      static int n = 0;\n"
      "      n++;\n"
      "      return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module c; int r; initial r = p::C::count(); endmodule\n"
      "module t;\n"
      "  c u1();\n"
      "  c u2();\n"
      "  int r;\n"
      "  initial #1 r = p::C::count();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(StaticMethodSimulation, UnitClassTaskStaticLocalSharedByEveryInstance) {
  auto val = RunAndGet(
      "class C;\n"
      "  static task count(output int r);\n"
      "    static int n = 0;\n"
      "    n++;\n"
      "    r = n;\n"
      "  endtask\n"
      "endclass\n"
      "module c; int r; initial C::count(r); endmodule\n"
      "module t;\n"
      "  c u1();\n"
      "  c u2();\n"
      "  int r;\n"
      "  initial #1 C::count(r);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

TEST(StaticMethodSimulation, SameNamedTasksOfTwoClassesKeepTheirOwnStatics) {
  const char* src =
      "class A;\n"
      "  static task count(output int r);\n"
      "    static int n = 0;\n"
      "    n++;\n"
      "    r = n;\n"
      "  endtask\n"
      "endclass\n"
      "class B;\n"
      "  static task count(output int r);\n"
      "    static int n = 10;\n"
      "    n++;\n"
      "    r = n;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin A::count(a); B::count(b); end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 1u);
  EXPECT_EQ(RunAndGet(src, "b"), 11u);
}

TEST(StaticMethodSimulation, StaticMethodIsCalledFromEachPlaceWithoutAnObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  static int current = 0;\n"
      "  static function int next_id(); next_id = ++current; endfunction\n"
      "endclass\n"
      "package k;\n"
      "  class PC; static function int two(); return 2; endfunction endclass\n"
      "  function int pf(); return PC::two(); endfunction\n"
      "endpackage\n"
      "function int uf(); return C::next_id(); endfunction\n"
      "class O; function int m(); return C::next_id(); endfunction endclass\n"
      "interface ifc; int r; initial r = C::next_id(); endinterface\n"
      "module t;\n"
      "  ifc i();\n"
      "  int r0, r1, r2, r3, r4, r5;\n"
      "  C h;\n"
      "  O o = new;\n"
      "  if (1) begin : g\n"
      "    int gr;\n"
      "    initial gr = C::next_id();\n"
      "  end\n"
      "  initial begin\n"
      "    #1 r0 = i.r + g.gr;\n"
      "    r1 = C::next_id();\n"
      "    r2 = h.next_id();\n"
      "    r3 = uf();\n"
      "    r4 = o.m();\n"
      "    r5 = k::pf();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"r0", 3u}, {"r1", 3u}, {"r2", 4u}, {"r3", 5u}, {"r4", 6u}, {"r5", 2u}});
}

TEST(StaticMethodSimulation, StaticMethodLocalsAreAutomatic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  static function int step(); int x; x++; return x; endfunction\n"
      "  static function int fact(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * fact(n - 1);\n"
      "  endfunction\n"
      "  static task slow(int d, output int o);\n"
      "    int x; x = d; #(d); o = x;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, o1, o2;\n"
      "  initial begin\n"
      "    r1 = C::step() * 10 + C::step();\n"
      "    r2 = C::fact(5);\n"
      "    fork C::slow(5, o1); C::slow(2, o2); join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 11u}, {"r2", 120u}, {"o1", 5u}, {"o2", 2u}});
}

}  // namespace
