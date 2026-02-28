// §8.24: Out-of-block declarations

#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_class_object.h"

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
// §8.24.1: Extern methods
// =============================================================================
TEST(ClassSim, ExternMethodRegisteredSeparately) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"val"});

  // Extern method body defined outside class.
  auto* extern_method = f.arena.Create<ModuleItem>();
  extern_method->kind = ModuleItemKind::kFunctionDecl;
  extern_method->name = "get_val";
  extern_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkId(f.arena, "val")));

  // Register it on the type (as if elaboration resolved the extern).
  type->methods["get_val"] = extern_method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("get_val");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_val");
}

}  // namespace
