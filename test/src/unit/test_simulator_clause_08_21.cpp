// §8.21: Abstract classes and pure virtual methods

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

// =============================================================================
// §8.21: Abstract classes and pure virtual methods
// =============================================================================
TEST(ClassSim, AbstractClassFlag) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "AbstractBase", {});
  abstract_type->is_abstract = true;

  EXPECT_TRUE(abstract_type->is_abstract);
}

TEST(ClassSim, PureVirtualMethodNullBody) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "Shape", {});
  abstract_type->is_abstract = true;

  // Pure virtual: vtable entry with nullptr method.
  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  EXPECT_EQ(abstract_type->vtable[0].method, nullptr);

  // Concrete derived class overrides it.
  auto* concrete = MakeClassType(f, "Circle", {"radius"});
  concrete->parent = abstract_type;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "area";
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 314)));
  concrete->vtable.push_back({"area", method, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  auto* resolved = obj->ResolveVirtualMethod("area");
  EXPECT_EQ(resolved, method);
}

}  // namespace
