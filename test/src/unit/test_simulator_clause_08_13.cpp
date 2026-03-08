#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, InheritanceParentLink) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  EXPECT_EQ(derived->parent, base);
  EXPECT_EQ(derived->parent->name, "Base");
}

TEST(ClassSim, InheritedMethodResolution) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_x";
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkId(f.arena, "x")));
  base->methods["get_x"] = method;

  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);

  auto* resolved = obj->ResolveMethod("get_x");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_x");
}

TEST(ClassSim, InheritanceChainPropertyAccess) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {"a"});
  auto* parent = MakeClassType(f, "Parent", {"b"});
  parent->parent = grand;
  auto* child = MakeClassType(f, "Child", {"c"});
  child->parent = parent;

  auto [handle, obj] = MakeObj(f, child);
  obj->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("c", f.arena).ToUint64(), 3u);
}

TEST(ClassSim, MethodResolutionWalksChain) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  auto* m = f.arena.Create<ModuleItem>();
  m->kind = ModuleItemKind::kFunctionDecl;
  m->name = "deep_method";
  base->methods["deep_method"] = m;

  auto [handle, obj] = MakeObj(f, leaf);
  auto* resolved = obj->ResolveMethod("deep_method");
  EXPECT_EQ(resolved, m);
}

// §8.13: IsA checks inheritance chain.
TEST(ClassSim, IsAReflexive) {
  SimFixture f;
  auto* type = MakeClassType(f, "A", {});
  EXPECT_TRUE(type->IsA(type));
}

TEST(ClassSim, IsADerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  EXPECT_TRUE(derived->IsA(base));
  EXPECT_FALSE(base->IsA(derived));
}

TEST(ClassSim, IsAMultiLevel) {
  SimFixture f;
  auto* a = MakeClassType(f, "A", {});
  auto* b = MakeClassType(f, "B", {});
  b->parent = a;
  auto* c = MakeClassType(f, "C", {});
  c->parent = b;

  EXPECT_TRUE(c->IsA(a));
  EXPECT_TRUE(c->IsA(b));
  EXPECT_FALSE(a->IsA(c));
}

// §8.13: Derived method overrides base method in resolution.
TEST(ClassSim, DerivedMethodOverridesBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "get";
  base->methods["get"] = base_method;

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;
  auto* derived_method = f.arena.Create<ModuleItem>();
  derived_method->kind = ModuleItemKind::kFunctionDecl;
  derived_method->name = "get";
  derived->methods["get"] = derived_method;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("get");
  EXPECT_EQ(resolved, derived_method);
}

}  // namespace
