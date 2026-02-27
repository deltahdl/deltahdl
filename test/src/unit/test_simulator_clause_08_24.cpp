// §8.24: Out-of-block declarations

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
// AST helper: make an identifier expression.
static Expr* MkId(Arena& a, std::string_view name) {
  auto* e = a.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
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

// Allocate a ClassObject of the given type, returning (handle_id, object*).
static std::pair<uint64_t, ClassObject*> MakeObj(SimFixture& f,
                                                 ClassTypeInfo* type) {
  auto* obj = f.arena.Create<ClassObject>();
  obj->type = type;
  // Initialize properties to 0.
  for (const auto& p : type->properties) {
    obj->properties[std::string(p.name)] =
        MakeLogic4VecVal(f.arena, p.width, 0);
  }
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  return {handle, obj};
}

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
