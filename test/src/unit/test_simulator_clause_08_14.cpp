// §8.14: Overridden members

#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_class_object.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
// AST helper: make an integer literal expression.
static Expr* MkInt(Arena& a, uint64_t val) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}
// Build a simple ClassTypeInfo and register it with the context.

// Allocate a ClassObject of the given type, returning (handle_id, object*).

namespace {

TEST(ClassSim, ChildMethodOverridesParent) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});

  auto* base_method = f.arena.Create<ModuleItem>();
  base_method->kind = ModuleItemKind::kFunctionDecl;
  base_method->name = "greet";
  base_method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 1)));
  base->methods["greet"] = base_method;

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;
  auto* child_method = f.arena.Create<ModuleItem>();
  child_method->kind = ModuleItemKind::kFunctionDecl;
  child_method->name = "greet";
  child_method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 2)));
  derived->methods["greet"] = child_method;

  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("greet");
  EXPECT_NE(resolved, nullptr);
  // Should find derived's version first.
  EXPECT_NE(resolved, base_method);
  EXPECT_EQ(resolved, child_method);
}

}  // namespace
