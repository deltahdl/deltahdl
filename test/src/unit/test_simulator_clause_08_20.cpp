#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
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

// §8.20: Virtual method dispatch through three-level hierarchy.
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

// §8.20: Non-virtual method dispatch does NOT use vtable.
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
  // ResolveMethod returns the derived's non-virtual method.
  EXPECT_EQ(obj->ResolveMethod("printA"), derived_method);
}

// §8.20: :final stored on ModuleItem.
TEST(ClassSim, MethodFinalFlag) {
  SimFixture f;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "locked";
  method->is_method_final = true;
  EXPECT_TRUE(method->is_method_final);
}

}  // namespace
