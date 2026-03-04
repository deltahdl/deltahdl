// §8.10: Static methods

#include "builders_ast.h"
#include "builders_systask.h"
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
// Build a simple ClassTypeInfo and register it with the context.

namespace {

TEST(ClassSim, StaticMethodResolution) {
  SimFixture f;
  auto* type = MakeClassType(f, "Util", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "helper";
  method->is_static = true;
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 100)));
  type->methods["helper"] = method;

  auto it = type->methods.find("helper");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

}  // namespace
