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

// A fixed-size formal may also receive a dynamic array of equal size. The
// elements are copied in by value and read back through the formal.
TEST(ArrayArgPassing, DynamicArrayEqualSizeToFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial result = second(d);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// Passing a dynamic array whose size differs from a fixed-size formal is the
// case the standard flags as requiring a run-time check: the mismatch is
// diagnosed when the call is bound.
TEST(ArrayArgPassing, DynamicArraySizeMismatchToFixedFormalRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial result = second(d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same equal-size run-time check governs a queue actual bound to a
// fixed-size formal.
TEST(ArrayArgPassing, QueueSizeMismatchToFixedFormalRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    result = second(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// An unsized formal dimension matches any size of the actual, so a formal that
// accepts a dynamic array can be passed a fixed-size array of compatible type.
TEST(ArrayArgPassing, FixedArrayToUnsizedDynamicFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 5; a[1] = 10; a[2] = 30; a[3] = 40;\n"
      "    result = third(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A dynamic array bound to an unsized formal is copied by value through the
// queue-backed representation, so the callee reads the actual's elements.
TEST(ArrayArgPassing, DynamicArrayToUnsizedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial result = third(d);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A queue of equal size binds to a fixed-size formal: its elements are copied
// in by value and read back through the formal.
TEST(ArrayArgPassing, QueueEqualSizeToFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    q.push_back(40);\n"
      "    result = second(q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// A queue bound to an unsized formal is copied by value into the formal's own
// queue-backed storage, so the callee reads the actual's elements.
TEST(ArrayArgPassing, QueueToUnsizedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    q.push_back(40);\n"
      "    result = third(q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// Because the bind makes an independent copy, mutating the formal inside the
// callee leaves the caller's dynamic array untouched.
TEST(ArrayArgPassing, DynamicArrayCallerUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{42, 7, 3};\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function int modify(int arr[3]);\n"
      "    arr[0] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    dummy = modify(d);\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
