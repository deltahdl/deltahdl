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

// 8.20: the 'virtual' qualifier is optional in a derived override; a method
// that overrides an inherited virtual method stays virtual, so dispatch
// through a base-typed handle reaches the derived body even though the
// override omits the keyword.
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

// §8.20 with §8.24: a virtual method whose body is declared out of the class
// block is still the one a call through a base-typed handle reaches, in the
// derived class that overrides it and in one that inherits it. The vtable
// entry has to hold the body and not the `extern` prototype, and the derived
// class copies the base's entries when it is lowered, so the base's body must
// be in place by then; a prototype in either place answers 0.
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

// §8.20 with §8.24 and §26.3: the same dispatch for classes a package
// declares, whose out-of-block bodies are the package's own items, reached
// through a wildcard import.
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

// §8.6 with §8.20: a method call whose return type is a class yields a handle,
// and a property selected on the call applies to the object returned, here the
// invoking object itself through `return this`. Read as a name, the select
// reached no object and answered 0; the sentinel tells that from the read.
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

// §8.6: each call in the chain applies to the object the call before it
// returned, so three levels deep the property read is the last object's.
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

// §8.6: a handle property selected on the call's result names the object it
// refers to, and the property read after it is that object's: the node
// `mk(6)` made links back to the node `mk(5)` made, whose v is 5.
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

// §8.6: a method called on a method call's result runs on the object the
// first call returned, the non-virtual `get` reading the v that `mk` set.
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

// §8.20: a virtual function's override may return a derived class type of the
// base's return type, and a virtual method called on that result dispatches
// by the returned object's type. `c` holds a D, so `some_method` is D's,
// returning a D whose n is the argument, and `who` is D's: 7 * 10 + 2. C's
// `who` answers 1, and a select that reaches no object answers 0.
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

}  // namespace
