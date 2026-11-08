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
                      "    static LinkedPacket lp = new;\n"
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
                      "    static LinkedPacket lp = new;\n"
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
                      "    static Derived d = new;\n"
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
                      "    static Derived d = new;\n"
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
                      "    static C c = new;\n"
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
                      "    static Derived d = new;\n"
                      "    result = d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            6u);
}

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
                      "    static Derived d = new;\n"
                      "    result = d.get_base();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

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

TEST(SuperSimulation, SuperNamesAnInheritedAssociativeProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Base;\n"
      "    int m[string];\n"
      "  endclass\n"
      "  class Sub extends Base;\n"
      "    function void fill(); m[\"a\"] = 9; super.m[\"b\"] = 4; "
      "endfunction\n"
      "    function int show(); return super.m.num() * 100 + super.m[\"a\"] * "
      "10\n"
      "      + m[\"b\"]; endfunction\n"
      "  endclass\n"
      "  Sub s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = new; s.fill();\n"
      "    result = s.show();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 294u);
}

TEST(SuperSimulation, SuperReachesAHiddenBaseAssociativeProperty) {
  auto v = RunAndGet(
      "module t;\n"
      "  class Base;\n"
      "    int m[string];\n"
      "    function int base_num(); return m.num(); endfunction\n"
      "  endclass\n"
      "  class Sub extends Base;\n"
      "    int m[string];\n"
      "    function void fill(); m[\"a\"] = 9; super.m[\"b\"] = 1;\n"
      "      super.m[\"c\"] = 2; endfunction\n"
      "    function int show(); return super.m.num() * 100 + m.num() * 10\n"
      "      + super.m[\"c\"]; endfunction\n"
      "  endclass\n"
      "  Sub s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = new; s.fill();\n"
      "    result = s.show() * 10 + s.base_num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2122u);
}

TEST(SuperSim, VirtualInterfaceMemberReadThroughSuper) {
  auto v = RunAndGet(
      "interface SBus; int a; endinterface\n"
      "class Base; virtual SBus vif; endclass\n"
      "class Derived extends Base;\n"
      "  function int sv(); return super.vif.a; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  SBus s();\n"
      "  Derived d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new; d.vif = s; s.a = 64;\n"
      "    result = d.sv();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 64u);
}

}  // namespace
