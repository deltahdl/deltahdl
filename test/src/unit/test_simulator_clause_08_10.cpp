#include "fixture_simulator.h"
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

}  // namespace
