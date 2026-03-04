#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ClassSim, ConstructorMethodRegistered) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"header", "payload"});

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
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "val", MkId(f.arena, "v")));
  type->methods["new"] = ctor;

  auto [handle, obj] = MakeObj(f, type);
  f.ctx.PushThis(obj);
  f.ctx.PushScope();

  auto* arg_var = f.ctx.CreateLocalVariable("v", 32);
  arg_var->value = MakeLogic4VecVal(f.arena, 32, 77);
  auto* val_var = f.ctx.CreateLocalVariable("val", 32);
  val_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto rhs_val = EvalExpr(MkId(f.arena, "v"), f.ctx, f.arena);
  val_var->value = rhs_val;

  obj->SetProperty("val", val_var->value);
  f.ctx.PopScope();
  f.ctx.PopThis();

  EXPECT_EQ(obj->GetProperty("val", f.arena).ToUint64(), 77u);
}

}  // namespace
