// §8.10: Static methods

#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

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
static ClassTypeInfo* MakeClassType(
    SimFixture& f, std::string_view name,
    const std::vector<std::string_view>& props) {
  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

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
