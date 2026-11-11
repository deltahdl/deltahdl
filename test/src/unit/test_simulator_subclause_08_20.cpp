#include <gtest/gtest.h>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, VirtualMethodDispatch) {
  SimFixture f;
  auto* base = MakeClassType(f, "Animal", {});
  auto* derived = MakeClassType(f, "Dog", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "speak";
  base_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkInt(f.arena, 0)));

  auto* derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "speak";
  derived_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkInt(f.arena, 1)));

  base->vtable.push_back({"speak", base_method, base});

  derived->vtable.push_back({"speak", derived_method, derived});

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveVirtualMethod("speak");
  EXPECT_EQ(resolved, derived_method);
}

TEST(ClassSim, VirtualMethodInheritedNotOverridden) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "action";

  base->vtable.push_back({"action", base_method, base});

  derived->vtable.push_back({"action", base_method, base});

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveVirtualMethod("action");
  EXPECT_EQ(resolved, base_method);
}

TEST(ClassSim, VTableFindIndex) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});

  auto* m1 = f.arena.Create<ModuleItem>();
  m1->kind = ModuleItemKind::kFunctionDecl;
  m1->name = "alpha";
  auto* m2 = f.arena.Create<ModuleItem>();
  m2->kind = ModuleItemKind::kFunctionDecl;
  m2->name = "beta";

  type->vtable.push_back({"alpha", m1, type});
  type->vtable.push_back({"beta", m2, type});

  EXPECT_EQ(type->FindVTableIndex("alpha"), 0);
  EXPECT_EQ(type->FindVTableIndex("beta"), 1);
  EXPECT_EQ(type->FindVTableIndex("gamma"), -1);
}

TEST(ClassSim, VirtualMethodNotFound) {
  SimFixture f;
  auto* type = MakeClassType(f, "Simple", {});
  auto [handle, obj] = MakeObj(f, type);

  auto* resolved = obj->ResolveVirtualMethod("nonexistent");
  EXPECT_EQ(resolved, nullptr);
}

TEST(ClassSim, EmptyVTable) {
  SimFixture f;
  auto* type = MakeClassType(f, "NoVirtuals", {});
  EXPECT_TRUE(type->vtable.empty());
  EXPECT_EQ(type->FindVTableIndex("anything"), -1);
}

TEST(ClassSim, VirtualMethodThreeLevelHierarchy) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = grand;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  auto* grand_method = f.arena.Create<ModuleItem>();
  grand_method->kind = ModuleItemKind::kFunctionDecl;
  grand_method->name = "action";

  auto* leaf_method = f.arena.Create<ModuleItem>();
  leaf_method->kind = ModuleItemKind::kFunctionDecl;
  leaf_method->name = "action";

  grand->vtable.push_back({"action", grand_method, grand});
  mid->vtable.push_back({"action", grand_method, grand});
  leaf->vtable.push_back({"action", leaf_method, leaf});

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("action"), leaf_method);
}

TEST(ClassSim, NonVirtualMethodUsesResolveMethod) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "printA";
  base->methods["printA"] = base_method;

  auto* derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "printA";
  derived->methods["printA"] = derived_method;

  auto [handle, obj] = MakeObj(f, derived);

  EXPECT_EQ(obj->ResolveMethod("printA"), derived_method);
}

TEST(ClassSim, MethodFinalFlag) {
  SimFixture f;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "locked";
  method->is_method_final = true;
  EXPECT_TRUE(method->is_method_final);
}

TEST(ClassSim, VirtualOverridesNonVirtualInVTable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "action";
  base->methods["action"] = base_method;

  auto* derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "action";
  derived->vtable.push_back({"action", derived_method, derived});

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_EQ(obj->ResolveVirtualMethod("action"), derived_method);
}

TEST(ClassSim, MethodInitialFlag) {
  SimFixture f;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "fresh";
  method->is_method_initial = true;
  EXPECT_TRUE(method->is_method_initial);
  EXPECT_FALSE(method->is_method_extends);
}

TEST(ClassSim, MethodExtendsFlag) {
  SimFixture f;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "override";
  method->is_method_extends = true;
  EXPECT_TRUE(method->is_method_extends);
  EXPECT_FALSE(method->is_method_initial);
}

TEST(ClassSim, FinalMethodInVTable) {
  SimFixture f;
  auto* type = MakeClassType(f, "Sealed", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "locked";
  method->is_method_final = true;
  type->vtable.push_back({"locked", method, type});

  EXPECT_EQ(type->FindVTableIndex("locked"), 0);
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ResolveVirtualMethod("locked"), method);
}

TEST(ClassSim, ImplicitOverrideWithoutVirtualKeywordDispatches) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual function int compute();\n"
                      "    compute = 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function int compute();\n"
                      "    compute = 2;\n"
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
            2u);
}

TEST(ClassSim, ExternVirtualBodyDispatchedThroughBaseHandle) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  extern virtual function int compute();\n"
                      "endclass\n"
                      "function int Base::compute();\n"
                      "  return 12;\n"
                      "endfunction\n"
                      "class Derived extends Base;\n"
                      "  extern virtual function int compute();\n"
                      "endclass\n"
                      "function int Derived::compute();\n"
                      "  return 21;\n"
                      "endfunction\n"
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
            21u);
}

TEST(ClassSim, ExternVirtualBodyInheritedByDerivedVTable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  extern virtual function int compute();\n"
                      "endclass\n"
                      "function int Base::compute();\n"
                      "  return 12;\n"
                      "endfunction\n"
                      "class Derived extends Base;\n"
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
            12u);
}

TEST(ClassSim, PackageExternVirtualBodyDispatchedThroughBaseHandle) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class Base;\n"
                      "    extern virtual function int compute();\n"
                      "  endclass\n"
                      "  function int Base::compute();\n"
                      "    return 12;\n"
                      "  endfunction\n"
                      "  class Derived extends Base;\n"
                      "    extern virtual function int compute();\n"
                      "  endclass\n"
                      "  function int Derived::compute();\n"
                      "    return 21;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "import p::*;\n"
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
            21u);
}

TEST(ClassSim, PropertyReadOnMethodCallResult) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  function Node self();\n"
                      "    return this;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  Node n = new;\n"
                      "  initial begin\n"
                      "    n.v = 30;\n"
                      "    r = n.self().v;\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            30u);
}

TEST(ClassSim, PropertyReadOnThreeChainedMethodCallResults) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  Node nxt;\n"
                      "  function Node mk(int x);\n"
                      "    Node n = new;\n"
                      "    n.v = x;\n"
                      "    n.nxt = this;\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  Node n = new;\n"
                      "  initial r = n.mk(1).mk(2).mk(3).v;\n"
                      "endmodule\n",
                      "r"),
            3u);
}

TEST(ClassSim, PropertyPathOnMethodCallResult) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  Node nxt;\n"
                      "  function Node mk(int x);\n"
                      "    Node n = new;\n"
                      "    n.v = x;\n"
                      "    n.nxt = this;\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  Node n = new;\n"
                      "  initial r = n.mk(5).mk(6).nxt.v;\n"
                      "endmodule\n",
                      "r"),
            5u);
}

TEST(ClassSim, MethodCalledOnMethodCallResult) {
  EXPECT_EQ(RunAndGet("class Node;\n"
                      "  int v;\n"
                      "  function Node mk(int x);\n"
                      "    Node n = new;\n"
                      "    n.v = x;\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "  function int get();\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  Node n = new;\n"
                      "  initial r = n.mk(30).get();\n"
                      "endmodule\n",
                      "r"),
            30u);
}

TEST(ClassSim, VirtualMethodCalledOnMethodCallResult) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  virtual function C some_method(int a);\n"
                      "    C c = new;\n"
                      "    return c;\n"
                      "  endfunction\n"
                      "  virtual function int who();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  int n;\n"
                      "  virtual function D some_method(int a);\n"
                      "    D d = new;\n"
                      "    d.n = a;\n"
                      "    return d;\n"
                      "  endfunction\n"
                      "  virtual function int who();\n"
                      "    return n * 10 + 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  C c;\n"
                      "  initial begin\n"
                      "    c = D::new;\n"
                      "    r = c.some_method(7).who();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            72u);
}

TEST(ClassSim, NonVirtualBaseMethodThroughBaseHandleIgnoresGrandchildVirtual) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  function int f1();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class A extends base;\n"
                      "  virtual function int f1();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  function int f1();\n"
                      "    return 3;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  base h;\n"
                      "  B b = new;\n"
                      "  initial begin\n"
                      "    h = b;\n"
                      "    r = h.f1() * 10 + b.f1();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            13u);
}

TEST(ClassSim, MethodVirtualFromMidClassDispatchesThroughMidHandle) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  function int f1();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class A extends base;\n"
                      "  virtual function int f1();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  function int f1();\n"
                      "    return 3;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  A h;\n"
                      "  B b = new;\n"
                      "  initial begin\n"
                      "    h = b;\n"
                      "    r = h.f1();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            3u);
}

TEST(ClassSim, VirtualMethodThroughBaseHandleStillDispatchesToDerived) {
  EXPECT_EQ(RunAndGet("class P;\n"
                      "  function int a();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "  virtual function int b();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Q extends P;\n"
                      "  function int a();\n"
                      "    return 3;\n"
                      "  endfunction\n"
                      "  virtual function int b();\n"
                      "    return 4;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  P h;\n"
                      "  Q q = new;\n"
                      "  initial begin\n"
                      "    h = q;\n"
                      "    r = h.a() * 10 + h.b();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            14u);
}

TEST(ClassSim, GrandchildVirtualInitialMethodThroughBaseAndMidHandles) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  function int f1();\n"
                      "    return 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class A extends base;\n"
                      "  function :initial int f1();\n"
                      "    return 2;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  virtual function :initial int f1();\n"
                      "    return 3;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int r = 99;\n"
                      "  base h;\n"
                      "  A a;\n"
                      "  B b = new;\n"
                      "  initial begin\n"
                      "    h = b;\n"
                      "    a = b;\n"
                      "    r = h.f1() * 100 + a.f1() * 10 + b.f1();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            123u);
}

TEST(ClassSim, ExtendsMakesAMethodVirtualAndInitialDoesNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class A; virtual function int f(); return 1; endfunction\n"
      "  virtual task t(output int r); r = 1; endtask endclass\n"
      "class B extends A; function :extends int f(); return 2; endfunction\n"
      "  task :extends t(output int r); r = 2; endtask endclass\n"
      "class C extends B; function int f(); return 3; endfunction\n"
      "  task t(output int r); r = 3; endtask endclass\n"
      "class A2; function int f(); return 1; endfunction endclass\n"
      "class B2 extends A2; function :initial int f(); return 2; endfunction "
      "endclass\n"
      "class C2 extends B2; function int f(); return 3; endfunction endclass\n"
      "class B3 extends A; extern function :extends int f(); endclass\n"
      "function int B3::f(); return 4; endfunction\n"
      "class C3 extends B3; function int f(); return 5; endfunction endclass\n"
      "class B4 extends A; function :extends :final int f(); return 6; "
      "endfunction endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8;\n"
      "  B b; C c = new; A a; B2 b2; C2 c2 = new; B3 b3; C3 c3 = new; B4 b4 = "
      "new;\n"
      "  initial begin\n"
      "    b = c; r1 = b.f();\n"
      "    a = c; r2 = a.f();\n"
      "    b2 = c2; r3 = b2.f();\n"
      "    b.t(r4);\n"
      "    a.t(r5);\n"
      "    b3 = c3; r6 = b3.f();\n"
      "    a = c3; r7 = a.f();\n"
      "    a = b4; r8 = a.f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u},
                    {"r2", 3u},
                    {"r3", 2u},
                    {"r4", 3u},
                    {"r5", 3u},
                    {"r6", 5u},
                    {"r7", 5u},
                    {"r8", 6u}});
}

}  // namespace
