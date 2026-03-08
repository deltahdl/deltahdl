#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(Functions, PassByRef) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 50);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ten";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kRef, false, {}, "r", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "r"),
                         MakeInt(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);

  auto* call = MakeCall(f.arena, "add_ten", {MakeId(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 60u);
}

TEST(Functions, PassByRefReadsCaller) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 25);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->func_args = {{Direction::kRef, false, {}, "r", nullptr, {}}};
  auto* body_expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "r"),
                               MakeInt(f.arena, 3));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 75u);
}

TEST(QueueRef, RefReadsCurrentValue) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, {}, "v", nullptr, {}}};
  func->func_body_stmts = {MakeReturn(f.arena, MakeId(f.arena, "v"))};
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeSelect(f.arena, "q", 1)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 20u);
}

TEST(Sim1352, RefImmediateVisibility) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "write_and_read";
  func->func_args = {{Direction::kRef, false, {}, "r", nullptr, {}}};

  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "r", MakeInt(f.arena, 42)));
  func->func_body_stmts.push_back(MakeReturn(f.arena, MakeId(f.arena, "r")));
  f.ctx.RegisterFunction("write_and_read", func);

  auto* call = MakeCall(f.arena, "write_and_read", {MakeId(f.arena, "x")});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 42u);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}
