#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SuperSimulation, SuperPropertyReturnsBaseValue) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int value;\n"
                      "  function new(); value = 10; endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  int value;\n"
                      "  function new(); super.new(); value = 20; endfunction\n"
                      "  function int get_base_value();\n"
                      "    return super.value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp = new;\n"
                      "    result = lp.get_base_value();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(SuperSimulation, SuperMethodCallDispatchesToBase) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int value;\n"
                      "  function new(); value = 3; endfunction\n"
                      "  function int delay();\n"
                      "    return value * value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class LinkedPacket extends Packet;\n"
                      "  int value;\n"
                      "  function new(); super.new(); value = 5; endfunction\n"
                      "  function int delay();\n"
                      "    return super.delay() + value * super.value;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    LinkedPacket lp = new;\n"
                      "    result = lp.delay();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            24u);
}

TEST(SuperSimulation, SuperAccessesInheritedMember) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 99; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function new(); super.new(); endfunction\n"
                      "  function int get();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(SuperSimulation, SuperPropertyWriteUpdatesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int x;\n"
                      "  function new(); super.new(); x = 2; endfunction\n"
                      "  function void set_base(int v);\n"
                      "    super.x = v;\n"
                      "  endfunction\n"
                      "  function int get_base();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    d.set_base(55);\n"
                      "    result = d.get_base();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(SuperSimulation, SuperReachesInheritedGrandparentMember) {
  EXPECT_EQ(RunAndGet("class A;\n"
                      "  int x;\n"
                      "  function new(); x = 10; endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  function new(); super.new(); endfunction\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  function new(); super.new(); endfunction\n"
                      "  function int get();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    result = c.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(SuperSimulation, SuperInitializationOrder) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 5; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new();\n"
                      "    super.new();\n"
                      "    y = super.x + 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            6u);
}

// §8.15 states the compiler inserts super.new automatically when the user
// constructor does not provide one, so the superclass is still initialized
// before the current class. Here the derived constructor omits super.new yet
// the base constructor's assignment to x is observed, proving the implicit
// call ran first.
TEST(SuperSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 7; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new(); y = 2; endfunction\n"
                      "  function int get_base();\n"
                      "    return super.x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.get_base();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

}  // namespace
