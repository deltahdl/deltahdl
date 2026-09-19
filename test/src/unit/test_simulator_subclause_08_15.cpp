#include <gtest/gtest.h>

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

// §8.15: a base class's method writes the property the base declares, and a
// read of that name through a handle to the derived object, from a method of
// another class, answers the same storage: no class between the object's type
// and the base declares the name again. The base constructor's write reached
// the base-scoped copy alone and the bare copy a handle read kept its default,
// so `child.v` read 0 where the constructor had stored 3.
TEST(SuperSim, BaseConstructorWriteReadThroughHandleFromAnotherClass) {
  EXPECT_EQ(RunAndGet("class InnerBase;\n"
                      "  int v;\n"
                      "  function new(int a);\n"
                      "    v = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Inner extends InnerBase;\n"
                      "  int k;\n"
                      "  function new();\n"
                      "    super.new(3);\n"
                      "    k = 9;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Plain;\n"
                      "  Inner child;\n"
                      "  int seen;\n"
                      "  function new();\n"
                      "    child = new;\n"
                      "    seen = child.v * 10 + child.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Plain p;\n"
                      "    p = new;\n"
                      "    result = p.seen * 100 + p.child.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3903u);
}

// §8.15: where the derived class declares the name again, the base's write
// stays the base's own -- the bare copy a handle read answers is the derived
// declaration's, which the base constructor's write leaves alone.
TEST(SuperSim, BaseWriteLeavesAShadowingDerivedPropertyAlone) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int v;\n"
                      "  function new(int a);\n"
                      "    v = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int v = 7;\n"
                      "  function new();\n"
                      "    super.new(3);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d;\n"
                      "    d = new;\n"
                      "    result = d.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

}  // namespace
