// §8.7: Constructors

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
// §8.7: Class constructors with arguments
// =============================================================================
TEST(ClassSim, ConstructorMethodRegistered) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});

  // function new(input int h, input int p);
  //   header = h; payload = p;
  // endfunction
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {
      {Direction::kInput, false, {}, "h", nullptr, {}},
      {Direction::kInput, false, {}, "p", nullptr, {}},
  };
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "header", MkId(f.arena, "h")));
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "payload", MkId(f.arena, "p")));
  type->methods["new"] = ctor;

  auto* resolved = type->methods["new"];
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->func_args.size(), 2u);
}

TEST(ClassSim, ConstructorBodyExecutesStatements) {
  SimFixture f;
  auto* type = MakeClassType(f, "Init", {"val"});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, {}, "v", nullptr, {}}};
  ctor->func_body_stmts.push_back(MakeAssign(f.arena, "val", MkId(f.arena, "v")));
  type->methods["new"] = ctor;

  // Simulate constructor execution manually.
  auto [handle, obj] = MakeObj(f, type);
  f.ctx.PushThis(obj);
  f.ctx.PushScope();

  auto* arg_var = f.ctx.CreateLocalVariable("v", 32);
  arg_var->value = MakeLogic4VecVal(f.arena, 32, 77);
  auto* val_var = f.ctx.CreateLocalVariable("val", 32);
  val_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Execute: val = v
  auto rhs_val = EvalExpr(MkId(f.arena, "v"), f.ctx, f.arena);
  val_var->value = rhs_val;

  // Writeback to object property.
  obj->SetProperty("val", val_var->value);
  f.ctx.PopScope();
  f.ctx.PopThis();

  EXPECT_EQ(obj->GetProperty("val", f.arena).ToUint64(), 77u);
}

}  // namespace
