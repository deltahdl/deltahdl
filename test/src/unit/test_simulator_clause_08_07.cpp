#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ClassConstructorSim, ConstructorAssignsProperty) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  integer command;\n"
                      "  function new();\n"
                      "    command = 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    result = p.command;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ClassConstructorSim, ConstructorWithArguments) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "  function new(int cmd, int addr);\n"
                      "    command = cmd;\n"
                      "    address = addr;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new(10, 20);\n"
                      "    result = p.command + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            30u);
}

TEST(ClassConstructorSim, ConstructorWithDefaultArgValues) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "  function new(int cmd = 5, int addr = 15);\n"
                      "    command = cmd;\n"
                      "    address = addr;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new;\n"
                      "    result = p.command + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(ClassConstructorSim, ImplicitConstructorCreatesObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.x = 99;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(ClassConstructorSim, PropertyExplicitDefaultInitialized) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x = 7;\n"
                      "  function new();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

// §8.7: a property with no explicit default is still initialized during
// construction — to its uninitialized value, not left absent. Reading the
// un-defaulted 2-state property straight after `new` yields 0, the other
// branch of the property-initialization rule from PropertyExplicitDefault.
TEST(ClassConstructorSim, UninitializedPropertyGetsDefault) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int with_default = 42;\n"
                      "  int no_default;\n"
                      "  function new();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.no_default;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §8.7: for the no-default branch, the uninitialized value follows the
// property's type. A 4-state property with no initializer comes out of
// construction holding X, not a forced 0 — observed via $isunknown.
TEST(ClassConstructorSim, FourStatePropertyUninitializedIsX) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  integer u;\n"
                      "  function new();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = $isunknown(c.u);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassConstructorSim, ConstructorBodyOverridesDefault) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int c1 = 1;\n"
                      "  int c2 = 1;\n"
                      "  function new();\n"
                      "    c2 = 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.c2;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

TEST(ClassConstructorSim, MultiplePropertiesWithDefaults) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a = 10;\n"
      "  int b = 20;\n"
      "  int c = 30;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb, rc;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    ra = obj.a;\n"
      "    rb = obj.b;\n"
      "    rc = obj.c;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 10u}, {"rb", 20u}, {"rc", 30u}});
}

TEST(ClassConstructorSim, ConstructorArgPassedToProperty) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int c1 = 1;\n"
                      "  int c2 = 1;\n"
                      "  int c3 = 1;\n"
                      "  function new(int a);\n"
                      "    c2 = 2;\n"
                      "    c3 = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new(99);\n"
                      "    result = c.c3;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §8.7: the derived constructor first runs the base constructor; once it
// completes, each property of the derived class is initialized (so d2, whose
// default reads the base property c2, sees the value the base constructor
// left), and only then does the rest of the derived body run. Mirrors the
// clause's C/D example. Built from §8.13 `extends` and §8.15 `super.new`.
TEST(ClassConstructorSim, DerivedConstructionOrderFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int c1 = 1;\n"
      "  int c2 = 1;\n"
      "  function new(int a);\n"
      "    c2 = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  int d1 = 4;\n"
      "  int d2 = c2;\n"
      "  int d3 = 6;\n"
      "  function new;\n"
      "    super.new(d3);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int rc1, rc2, rd1, rd2, rd3;\n"
      "  initial begin\n"
      "    D obj;\n"
      "    obj = new;\n"
      "    rc1 = obj.c1;\n"
      "    rc2 = obj.c2;\n"
      "    rd1 = obj.d1;\n"
      "    rd2 = obj.d2;\n"
      "    rd3 = obj.d3;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"rc1", 1u}, {"rc2", 2u}, {"rd1", 4u}, {"rd2", 2u}, {"rd3", 6u}});
}

// §8.7: even when the derived class supplies no explicit constructor, its
// implicit `new` first runs the base constructor. Constructing the child
// therefore leaves the base property set by the base body. Built from §8.13
// `extends` with an implicit derived constructor.
TEST(ClassConstructorSim, ImplicitConstructorInvokesBaseConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new();\n"
                      "    x = 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Child extends Base;\n"
                      "  int y;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Child c;\n"
                      "    c = new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

// §8.7: constructor argument conventions match ordinary subroutine calls, so a
// call may supply some actuals positionally and let the rest fall back to their
// declared defaults. new(7) binds cmd=7 and leaves addr at its default 15.
TEST(ClassConstructorSim, ConstructorPartialDefaultArgs) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "  function new(int cmd = 5, int addr = 15);\n"
                      "    command = cmd;\n"
                      "    address = addr;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new(7);\n"
                      "    result = p.command + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            22u);
}

// §8.7: `new` construction also occurs in the declaration-initializer position
// (`Type v = new;`), not only in a standalone procedural assignment. The
// constructor body runs and its property assignment is observable.
TEST(ClassConstructorSim, DeclarationInitializerConstructs) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new();\n"
                      "    x = 55;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

}  // namespace
