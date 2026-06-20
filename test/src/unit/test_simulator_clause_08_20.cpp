#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
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

}  // namespace
