#include <gtest/gtest.h>

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

TEST(ClassConstructorSim, DerivedInitializerSeesBaseConstructorWrite) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int b = 1;\n"
                      "  function new();\n"
                      "    b = 5;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int d = b;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived obj;\n"
                      "    obj = new;\n"
                      "    result = obj.d;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

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
                      "    static C c = new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(ClassConstructorSim, ConstructorConstructsClassHandleProperty) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int q;\n"
                      "  function new();\n"
                      "    q = 31;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner inner;\n"
                      "  function new();\n"
                      "    inner = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Outer o = new;\n"
                      "    result = o.inner.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            31u);
}

TEST(ClassConstructorSim, ClassHandlePropertyIsNullUntilConstructed) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int q;\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner inner;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Outer o = new;\n"
                      "    result = (o.inner == null) ? 1 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(ClassConstructorSim, ConstructorConstructsThisQualifiedHandleProperty) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int q;\n"
                      "  function new();\n"
                      "    q = 44;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner inner;\n"
                      "  function new();\n"
                      "    this.inner = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Outer o = new;\n"
                      "    result = o.inner.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            44u);
}

TEST(ClassConstructorSim, MethodConstructsClassHandleProperty) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int q;\n"
                      "  function new();\n"
                      "    q = 17;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner inner;\n"
                      "  function void build();\n"
                      "    inner = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Outer o = new;\n"
                      "    o.build();\n"
                      "    result = o.inner.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            17u);
}

TEST(ClassConstructorSim, TwoStateInitializerLeavesItsSourcesXBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C;\n"
      "  logic [7:0] tag = 8'hx5;\n"
      "  bit [7:0] snap = tag;\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] carried;\n"
      "  int taken;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    carried = c.tag;\n"
      "    taken = c.snap;\n"
      "  end\n"
      "endmodule\n",
      f, "carried");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "xxxx0101");
  auto* taken = f.ctx.FindVariable("taken");
  ASSERT_NE(taken, nullptr);
  EXPECT_EQ(taken->value.ToUint64(), 5u);
}

TEST(ClassConstructorSim,
     InitializerOfAnUnsizedTypeDoesNotShareItsSourcesBuffer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  pair_t s;\n"
      "  class C;\n"
      "    pair_t snap = s;\n"
      "  endclass\n"
      "  logic [15:0] got;\n"
      "  initial begin\n"
      "    C c;\n"
      "    s = 16'hAAxB;\n"
      "    c = new;\n"
      "    s.b = 8'h00;\n"
      "    got = c.snap;\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10101010xxxx1011");
}

TEST(ClassConstructorSim, InitializerOfAnUnsizedTypeIsOwnedUnderTheScopedKey) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  pair_t s;\n"
      "  class C;\n"
      "    pair_t snap = s;\n"
      "    function logic [15:0] held();\n"
      "      return snap;\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [15:0] got;\n"
      "  initial begin\n"
      "    C c;\n"
      "    s = 16'hAAxB;\n"
      "    c = new;\n"
      "    s.b = 8'h00;\n"
      "    got = c.held();\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10101010xxxx1011");
}

TEST(ClassConstructorSim, NewCallBindsArgumentsByName) {
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
                      "    p = new(.addr(3), .cmd(5));\n"
                      "    result = p.command * 10 + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            53u);
}

TEST(ClassConstructorSim, NewCallBindsAnOrderedThenANamedArgument) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "  function new(int cmd, int addr = 4);\n"
                      "    command = cmd;\n"
                      "    address = addr;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new(9, .addr(4));\n"
                      "    result = p.command * 10 + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            94u);
}

TEST(ClassConstructorSim, NewCallNamedArgumentWithoutAValueTakesTheDefault) {
  EXPECT_EQ(RunAndGet("class Packet;\n"
                      "  int command;\n"
                      "  int address;\n"
                      "  function new(int cmd, int addr = 7);\n"
                      "    command = cmd;\n"
                      "    address = addr;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Packet p;\n"
                      "    p = new(.addr(), .cmd(2));\n"
                      "    result = p.command * 10 + p.address;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            27u);
}

TEST(ClassConstructorSim,
     StaticMethodConstructsTheStaticHandlePropertyItTests) {
  EXPECT_EQ(RunAndGet("class root;\n"
                      "  static root m_inst;\n"
                      "  int tag = 7;\n"
                      "  static function root in_direct();\n"
                      "    if (m_inst == null) m_inst = new();\n"
                      "    return m_inst;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root a, b;\n"
                      "    a = root::in_direct();\n"
                      "    b = root::in_direct();\n"
                      "    result = (a != null && a == b) ? a.tag : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(ClassConstructorSim,
     OutOfBlockStaticMethodConstructsAStaticHandleProperty) {
  EXPECT_EQ(RunAndGet("class root;\n"
                      "  static root m_inst;\n"
                      "  int tag = 23;\n"
                      "  extern static function root out_direct();\n"
                      "endclass\n"
                      "function root root::out_direct();\n"
                      "  m_inst = new();\n"
                      "  return m_inst;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root c;\n"
                      "    c = root::out_direct();\n"
                      "    result = (c == null) ? 0 : c.tag;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            23u);
}

TEST(ClassConstructorSim,
     StaticMethodReachedFromAnInstanceConstructsTheClassesStorage) {
  EXPECT_EQ(RunAndGet("class leaf;\n"
                      "  int q = 41;\n"
                      "endclass\n"
                      "class root;\n"
                      "  static leaf m_inst;\n"
                      "  static function void build();\n"
                      "    m_inst = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class caller;\n"
                      "  function void go();\n"
                      "    root::build();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static caller c = new;\n"
                      "    leaf l;\n"
                      "    c.go();\n"
                      "    l = root::m_inst;\n"
                      "    result = (l == null) ? 0 : l.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            41u);
}

TEST(ClassConstructorSim,
     InstanceMethodConstructsAHandlePropertyWithParenthesizedNew) {
  EXPECT_EQ(RunAndGet("class Inner;\n"
                      "  int q = 29;\n"
                      "endclass\n"
                      "class Outer;\n"
                      "  Inner child;\n"
                      "  function void build();\n"
                      "    child = new();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static Outer o = new;\n"
                      "    o.build();\n"
                      "    result = (o.child == null) ? 0 : o.child.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            29u);
}

TEST(ClassConstructorSim,
     ClassScopedStaticHandlePropertyConstructedFromAModule) {
  EXPECT_EQ(RunAndGet("class leaf;\n"
                      "  int q = 53;\n"
                      "endclass\n"
                      "class root;\n"
                      "  static leaf m_inst;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    leaf l;\n"
                      "    root::m_inst = new;\n"
                      "    l = root::m_inst;\n"
                      "    result = (l == null) ? 0 : l.q;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            53u);
}

TEST(ClassConstructorSim, NewArgumentsReadTheCallersObject) {
  EXPECT_EQ(RunAndGet("class node;\n"
                      "  int depth;\n"
                      "  function new(int d);\n"
                      "    depth = d;\n"
                      "  endfunction\n"
                      "  function node child();\n"
                      "    node next;\n"
                      "    next = new(depth - 1);\n"
                      "    return next;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    node root, c;\n"
                      "    root = new(4);\n"
                      "    c = root.child();\n"
                      "    result = c.depth * 10 + root.depth;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            34u);
}

}  // namespace
