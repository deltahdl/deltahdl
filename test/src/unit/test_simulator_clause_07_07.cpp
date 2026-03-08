#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ArrayArgPassing, CopyByValue) {
  FuncFixture f;

  MakeArray4(f, "src");

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_elem";
  func->is_automatic = true;
  FunctionArg arg;
  arg.direction = Direction::kInput;
  arg.data_type.kind = DataTypeKind::kInt;
  arg.name = "arr";

  arg.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg);

  auto* ret_expr = MakeSelect(f.arena, "arr", 1);
  func->func_body_stmts.push_back(MakeReturn(f.arena, ret_expr));
  f.ctx.RegisterFunction("read_elem", func);

  auto* call = MakeCall(f.arena, "read_elem", {MakeId(f.arena, "src")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(ArrayArgPassing, CopySemantics) {
  FuncFixture f;

  MakeArray4(f, "src");

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "modify_arr";
  func->is_automatic = true;
  FunctionArg arg;
  arg.direction = Direction::kInput;
  arg.data_type.kind = DataTypeKind::kInt;
  arg.name = "arr";
  arg.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg);

  auto* lhs = MakeSelect(f.arena, "arr", 0);
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = MakeInt(f.arena, 99);
  func->func_body_stmts.push_back(assign);
  func->func_body_stmts.push_back(
      MakeReturn(f.arena, MakeSelect(f.arena, "arr", 0)));
  f.ctx.RegisterFunction("modify_arr", func);

  auto* call = MakeCall(f.arena, "modify_arr", {MakeId(f.arena, "src")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);

  auto* orig = f.ctx.FindVariable("src[0]");
  ASSERT_NE(orig, nullptr);
  EXPECT_EQ(orig->value.ToUint64(), 10u);
}

}
