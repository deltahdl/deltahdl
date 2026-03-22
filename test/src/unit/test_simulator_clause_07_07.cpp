#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_scheduler.h"
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

// §7.7: End-to-end pass-by-value — function reads array element.
TEST(ArrayArgPassing, PassByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    result = second(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// §7.7: End-to-end copy semantics — modifying formal does not affect actual.
TEST(ArrayArgPassing, CopySemanticsEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int result;\n"
      "  function int modify(int arr[3]);\n"
      "    arr[0] = 999;\n"
      "    return arr[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 5; a[1] = 10; a[2] = 15;\n"
      "    result = modify(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 999u);
}

// §7.7: Caller's array is unchanged after function modifies its copy.
TEST(ArrayArgPassing, CallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[2];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function int modify(int arr[2]);\n"
      "    arr[0] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 42; a[1] = 7;\n"
      "    dummy = modify(a);\n"
      "    result = a[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.7: Multiple array arguments passed to a single function.
TEST(ArrayArgPassing, MultipleArrayArgs) {
  FuncFixture f;

  MakeArray4(f, "x");
  MakeArray4(f, "y");

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "sum_first";
  func->is_automatic = true;

  FunctionArg arg_a;
  arg_a.direction = Direction::kInput;
  arg_a.data_type.kind = DataTypeKind::kInt;
  arg_a.name = "a";
  arg_a.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg_a);

  FunctionArg arg_b;
  arg_b.direction = Direction::kInput;
  arg_b.data_type.kind = DataTypeKind::kInt;
  arg_b.name = "b";
  arg_b.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg_b);

  auto* a0 = MakeSelect(f.arena, "a", 0);
  auto* b0 = MakeSelect(f.arena, "b", 0);
  auto* sum = MakeBinary(f.arena, TokenKind::kPlus, a0, b0);
  func->func_body_stmts.push_back(MakeReturn(f.arena, sum));
  f.ctx.RegisterFunction("sum_first", func);

  auto* call = MakeCall(f.arena, "sum_first",
                        {MakeId(f.arena, "x"), MakeId(f.arena, "y")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

// §7.7: All elements are copied, not just the first.
TEST(ArrayArgPassing, AllElementsCopied) {
  FuncFixture f;

  MakeArray4(f, "src");

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_last";
  func->is_automatic = true;
  FunctionArg arg;
  arg.direction = Direction::kInput;
  arg.data_type.kind = DataTypeKind::kInt;
  arg.name = "arr";
  arg.unpacked_dims.push_back(MakeInt(f.arena, 4));
  func->func_args.push_back(arg);

  auto* ret_expr = MakeSelect(f.arena, "arr", 3);
  func->func_body_stmts.push_back(MakeReturn(f.arena, ret_expr));
  f.ctx.RegisterFunction("read_last", func);

  auto* call = MakeCall(f.arena, "read_last", {MakeId(f.arena, "src")});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 40u);
}

}  // namespace
