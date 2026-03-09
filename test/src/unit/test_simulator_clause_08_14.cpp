#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, ChildMethodOverridesParent) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "greet";
  base_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkInt(f.arena, 1)));
  base->methods["greet"] = base_method;

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;
  auto* child_method = f.arena.Create<ModuleItem>();
  child_method->kind = ModuleItemKind::kFunctionDecl;
  child_method->name = "greet";
  child_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkInt(f.arena, 2)));
  derived->methods["greet"] = child_method;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("greet");
  EXPECT_NE(resolved, nullptr);

  EXPECT_NE(resolved, base_method);
  EXPECT_EQ(resolved, child_method);
}

TEST(ClassSim, SubclassIsValidBaseObject) {
  SimFixture f;
  auto* packet = MakeClassType(f, "Packet", {"i"});
  auto* linked = MakeClassType(f, "LinkedPacket", {"i"});
  linked->parent = packet;

  EXPECT_TRUE(linked->IsA(packet));
  EXPECT_FALSE(packet->IsA(linked));
}

TEST(ClassSim, NonVirtualResolutionFromBaseType) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* base_get = f.arena.Create<ModuleItem>();
  base_get->kind = ModuleItemKind::kFunctionDecl;
  base_get->name = "get";
  base->methods["get"] = base_get;

  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;
  auto* derived_get = f.arena.Create<ModuleItem>();
  derived_get->kind = ModuleItemKind::kFunctionDecl;
  derived_get->name = "get";
  derived->methods["get"] = derived_get;

  auto [h1, obj1] = MakeObj(f, derived);
  EXPECT_EQ(obj1->ResolveMethod("get"), derived_get);

  auto it = base->methods.find("get");
  ASSERT_NE(it, base->methods.end());
  EXPECT_EQ(it->second, base_get);
}

TEST(ClassSim, OverriddenPropertyInDerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"i"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"i"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  obj->SetProperty("i", MakeLogic4VecVal(f.arena, 32, 2));

  EXPECT_EQ(obj->GetProperty("i", f.arena).ToUint64(), 2u);
}

TEST(ClassSim, InheritedMethodNotOverridden) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "status";
  base->methods["status"] = base_method;

  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("status");
  EXPECT_EQ(resolved, base_method);
}

}  // namespace
