#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, NonVirtualFallbackToStaticResolution) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "bar";
  type->methods["bar"] = method;

  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->ResolveVirtualMethod("bar"), nullptr);

  EXPECT_EQ(obj->ResolveMethod("bar"), method);
}

TEST(ClassSim, PolymorphicUnknownMethodReturnsNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ResolveVirtualMethod("nonexistent"), nullptr);
  EXPECT_EQ(obj->ResolveMethod("nonexistent"), nullptr);
}

TEST(ClassSim, E2eVirtualDispatchThroughBaseVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual function int compute();\n"
                      "    compute = 10;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  virtual function int compute();\n"
                      "    compute = 20;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    b = d;\n"
                      "    result = b.compute();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

// Late binding is not limited to virtual functions: a virtual task called
// through a superclass handle likewise resolves to the override belonging to
// the object's dynamic type. The task reports through an output argument.
TEST(ClassSim, E2eVirtualTaskDispatchThroughBaseVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual task get(output int v);\n"
                      "    v = 10;\n"
                      "  endtask\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  virtual task get(output int v);\n"
                      "    v = 20;\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    b = d;\n"
                      "    b.get(result);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(ClassSim, E2eVirtualDispatchThreeLevelsThroughBase) {
  EXPECT_EQ(RunAndGet("class Grand;\n"
                      "  virtual function int level();\n"
                      "    level = 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Mid extends Grand;\n"
                      "  virtual function int level();\n"
                      "    level = 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Leaf extends Mid;\n"
                      "  virtual function int level();\n"
                      "    level = 3;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Grand g;\n"
                      "    Leaf lf;\n"
                      "    lf = new;\n"
                      "    g = lf;\n"
                      "    result = g.level();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ClassSim, E2eInheritedVirtualThroughBaseVariable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual function int compute();\n"
                      "    compute = 10;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Mid extends Base;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    Mid m;\n"
                      "    m = new;\n"
                      "    b = m;\n"
                      "    result = b.compute();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

TEST(ClassSim, E2eSelectiveOverrideThroughBaseVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  virtual function int send();\n"
      "    send = 10;\n"
      "  endfunction\n"
      "  virtual function int receive();\n"
      "    receive = 20;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  virtual function int send();\n"
      "    send = 99;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r_send, r_recv;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    b = d;\n"
      "    r_send = b.send();\n"
      "    r_recv = b.receive();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r_send", 99u}, {"r_recv", 20u}});
}

TEST(ClassSim, E2eHeterogeneousDispatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class BasePacket;\n"
      "  virtual function int tag();\n"
      "    tag = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "class EtherPacket extends BasePacket;\n"
      "  virtual function int tag();\n"
      "    tag = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class TokenPacket extends BasePacket;\n"
      "  virtual function int tag();\n"
      "    tag = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r0, r1;\n"
      "  initial begin\n"
      "    BasePacket b0, b1;\n"
      "    EtherPacket ep;\n"
      "    TokenPacket tp;\n"
      "    ep = new;\n"
      "    tp = new;\n"
      "    b0 = ep;\n"
      "    b1 = tp;\n"
      "    r0 = b0.tag();\n"
      "    r1 = b1.tag();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r0", 1u}, {"r1", 2u}});
}

TEST(ClassSim, E2eDispatchChangesOnReassignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  virtual function int id();\n"
      "    id = 0;\n"
      "  endfunction\n"
      "endclass\n"
      "class SubA extends Base;\n"
      "  virtual function int id();\n"
      "    id = 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class SubB extends Base;\n"
      "  virtual function int id();\n"
      "    id = 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    SubA a;\n"
      "    SubB sb;\n"
      "    a = new;\n"
      "    sb = new;\n"
      "    b = a;\n"
      "    r1 = b.id();\n"
      "    b = sb;\n"
      "    r2 = b.id();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 2u}});
}

TEST(ClassSim, E2eAbstractBaseVariableDispatch) {
  EXPECT_EQ(RunAndGet("virtual class BasePacket;\n"
                      "  pure virtual function int send();\n"
                      "endclass\n"
                      "class EtherPacket extends BasePacket;\n"
                      "  virtual function int send();\n"
                      "    send = 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    BasePacket bp;\n"
                      "    EtherPacket ep;\n"
                      "    ep = new;\n"
                      "    bp = ep;\n"
                      "    result = bp.send();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

}  // namespace
