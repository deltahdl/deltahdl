// §8.13: Inheritance and subclasses

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// AST helper: make an identifier expression.
static Expr* MkId(Arena& a, std::string_view name) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Build a simple ClassTypeInfo and register it with the context.

// Allocate a ClassObject of the given type, returning (handle_id, object*).

namespace {

// =============================================================================
// §8.13: Inheritance with `extends`
// =============================================================================
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
  // Should find get_x from base class.
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

  // Only base defines the method.
  auto* m = f.arena.Create<ModuleItem>();
  m->kind = ModuleItemKind::kFunctionDecl;
  m->name = "deep_method";
  base->methods["deep_method"] = m;

  auto [handle, obj] = MakeObj(f, leaf);
  auto* resolved = obj->ResolveMethod("deep_method");
  EXPECT_EQ(resolved, m);
}

}  // namespace
