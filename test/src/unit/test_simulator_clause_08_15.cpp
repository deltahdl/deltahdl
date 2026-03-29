#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SuperSimulation, SuperMethodResolutionFromParent) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* base_delay = f.arena.Create<ModuleItem>();
  base_delay->kind = ModuleItemKind::kFunctionDecl;
  base_delay->name = "delay";
  base->methods["delay"] = base_delay;

  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;
  auto* derived_delay = f.arena.Create<ModuleItem>();
  derived_delay->kind = ModuleItemKind::kFunctionDecl;
  derived_delay->name = "delay";
  derived->methods["delay"] = derived_delay;

  auto it = base->methods.find("delay");
  ASSERT_NE(it, base->methods.end());
  EXPECT_EQ(it->second, base_delay);
}

TEST(SuperSimulation, SuperPropertyAccessFromBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"value"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"value"});
  derived->parent = base;

  EXPECT_EQ(base->properties.size(), 1u);
  EXPECT_EQ(derived->properties.size(), 1u);
  EXPECT_EQ(base->properties[0].name, "value");
  EXPECT_EQ(derived->properties[0].name, "value");
}

TEST(SuperSimulation, SuperParentAccessible) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* mid = MakeClassType(f, "Mid", {"y"});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {"z"});
  leaf->parent = mid;

  EXPECT_EQ(leaf->parent, mid);
  EXPECT_EQ(leaf->parent->name, "Mid");

  EXPECT_EQ(leaf->parent->parent, base);
}

TEST(SuperSimulation, SuperPropertyReturnsBaseValue) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
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
      "endmodule\n", "result"), 10u);
}

TEST(SuperSimulation, SuperMethodCallDispatchesToBase) {
  EXPECT_EQ(RunAndGet(
      "class Packet;\n"
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
      "endmodule\n", "result"), 24u);  // 3*3 + 5*3 = 9 + 15 = 24
}

TEST(SuperSimulation, SuperNewWithArgsInitializesBase) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(int v); x = v; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function new(int v); super.new(v); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new(42);\n"
      "    result = d.x;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(SuperSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  int x;\n"
      "  function new(); x = 7; endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d = new;\n"
      "    result = d.x;\n"
      "  end\n"
      "endmodule\n", "result"), 7u);
}

TEST(SuperSimulation, SuperAccessesInheritedMember) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
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
      "endmodule\n", "result"), 99u);
}

TEST(SuperSimulation, SuperPropertyWriteUpdatesBase) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
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
      "endmodule\n", "result"), 55u);
}

TEST(SuperSimulation, SuperReachesInheritedGrandparentMember) {
  EXPECT_EQ(RunAndGet(
      "class A;\n"
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
      "endmodule\n", "result"), 10u);
}

TEST(SuperSimulation, SuperInitializationOrder) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
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
      "endmodule\n", "result"), 6u);
}

}  // namespace
