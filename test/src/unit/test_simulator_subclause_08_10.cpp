#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.10: a static method behaves like a regular subroutine that can be called
// with no class instantiation. Here no object of Util is ever constructed, yet
// the scope-resolved call runs and yields a computed result.
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

// §8.10: a static method may directly access static class properties. The
// static property carries a §8.9 inline initializer, so the value observed
// through the static method is the one produced by that declaration.
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

// §8.10: the static-method form applies to tasks as well as functions. A
// static task, called without an instance, writes shared static state that a
// static function then reads back.
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

// §8.10: a static method is called with no object of its class, and §8.21 has
// an abstract class that can never have one; a wildcard import in the
// compilation-unit scope (§3.12.1, §26.3) makes the package's class visible to
// the module by its bare name. The call through the class scope resolution
// operator yields the method's 7, where a lookup that misses the class yields
// the zero of an unresolved call.
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

// §8.10: a static method reads and writes the static properties of its class,
// of which §8.9 keeps one copy. The class is named by its bare name through the
// module's import and by `p::cnt_t` through the package scope resolution
// operator of §26.3; both calls reach the one copy of `total`, so the second
// answers 38, where a class lowered once per spelling would answer 34.
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

// §8.10 with §13.3: a static task runs in class scope with no `this`, and a
// delay in its body suspends the enabling process as any task's does, so the
// static property it writes after `#3` is read at time 3 and the enabling
// process goes on after it. A static task named through the class scope,
// `Counter::run()`, and through a handle, `h.run()`, are the same call
// (§8.10). Before the fix the call fell to the synchronous function path,
// which drops a delay, so the write landed at time 0 or not at all: the
// result reads the time of the write and the property, 3 * 100 + 6 + 3 * 10
// + 6 for the two calls.
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

// §8.10 with §9.3.2: a fork inside a static task, its branches writing a
// static property after `#3` and the task's own local after `#1`, joined
// before the task reads both at time 3 -- the Clause 9 discovery's probe 84.
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

}  // namespace
