#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// §7.7: Array argument is copied by value into the called function.
TEST(ArrayArgPassing, CopyByValue) {
  FuncFixture f;

  // Create source array: src[0..3] = {10,20,30,40}
  MakeArray4(f, "src");

  // Create a function that reads arr[1] and returns it.
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_elem";
  func->is_automatic = true;
  FunctionArg arg;
  arg.direction = Direction::kInput;
  arg.data_type.kind = DataTypeKind::kInt;
  arg.name = "arr";
  // Mark as array arg with size dim.
  arg.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg);
  // Body: return arr[1];
  auto* ret_expr = MakeSelect(f.arena, "arr", 1);
  func->func_body_stmts.push_back(MakeReturn(f.arena, ret_expr));
  f.ctx.RegisterFunction("read_elem", func);

  // Call: read_elem(src)
  auto* call = MakeCall(f.arena, "read_elem", {MakeId(f.arena, "src")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

// §7.7: Modifying the formal array does not affect the actual.
TEST(ArrayArgPassing, CopySemantics) {
  FuncFixture f;

  // Create source array: src[0..3] = {10,20,30,40}
  MakeArray4(f, "src");

  // Create a function that writes arr[0] = 99, then returns arr[0].
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
  // Body: arr[0] = 99; return arr[0];
  auto* lhs = MakeSelect(f.arena, "arr", 0);
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = MakeInt(f.arena, 99);
  func->func_body_stmts.push_back(assign);
  func->func_body_stmts.push_back(
      MakeReturn(f.arena, MakeSelect(f.arena, "arr", 0)));
  f.ctx.RegisterFunction("modify_arr", func);

  // Call: modify_arr(src) — should return 99.
  auto* call = MakeCall(f.arena, "modify_arr", {MakeId(f.arena, "src")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);

  // Original src[0] should still be 10 (copy semantics).
  auto* orig = f.ctx.FindVariable("src[0]");
  ASSERT_NE(orig, nullptr);
  EXPECT_EQ(orig->value.ToUint64(), 10u);
}

}  // namespace
