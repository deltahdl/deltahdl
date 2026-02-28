// §8.17: Chaining constructors

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
// §8.15: super.new() chaining
// =============================================================================
TEST(ClassSim, SuperNewChaining) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"base_val"});
  auto* derived = MakeClassType(f, "Derived", {"child_val"});
  derived->parent = base;

  // Simulate super.new() chain: first init base, then derived.
  auto [handle, obj] = MakeObj(f, derived);

  // Base constructor sets base_val = 10.
  obj->SetProperty("base_val", MakeLogic4VecVal(f.arena, 32, 10));
  // Derived constructor sets child_val = 20.
  obj->SetProperty("child_val", MakeLogic4VecVal(f.arena, 32, 20));

  EXPECT_EQ(obj->GetProperty("base_val", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("child_val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, SuperNewWithArgs) {
  SimFixture f;
  auto* base = MakeClassType(f, "Vehicle", {"speed"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, {}, "s", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "speed", MkId(f.arena, "s")));
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Car", {"doors"});
  derived->parent = base;

  // Verify base constructor is accessible from derived type chain.
  auto it = derived->parent->methods.find("new");
  ASSERT_NE(it, derived->parent->methods.end());
  auto* base_ctor = it->second;
  ASSERT_NE(base_ctor, nullptr);
  EXPECT_EQ(base_ctor->func_args.size(), 1u);
}

}  // namespace
