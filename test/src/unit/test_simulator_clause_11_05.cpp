#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(Eval, VariableReferenceUsesAllBits) {
  ExprFixture f;
  auto* var = f.ctx.CreateVariable("wide", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xDEADBEEF);

  auto result = EvalExpr(MakeId(f.arena, "wide"), f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 0xDEADBEEFu);
}

TEST(Eval, SingleBitVariableUsesAllBits) {
  ExprFixture f;
  auto* var = f.ctx.CreateVariable("flag", 1);
  var->value = MakeLogic4VecVal(f.arena, 1, 1);

  auto result = EvalExpr(MakeId(f.arena, "flag"), f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Eval, ConcatenationAsOperand) {
  ExprFixture f;
  auto* concat = MakeConcatOfTwoVars(f, "hi", 4, 0xA, "lo", 4, 0x5);

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xA5u);
}

TEST(Eval, NestedConcatenationAsOperand) {
  ExprFixture f;
  auto* va = f.ctx.CreateVariable("a", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0x1);
  auto* vb = f.ctx.CreateVariable("b", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0x2);
  auto* vc = f.ctx.CreateVariable("c", 4);
  vc->value = MakeLogic4VecVal(f.arena, 4, 0x3);

  auto* inner = f.arena.Create<Expr>();
  inner->kind = ExprKind::kConcatenation;
  inner->elements.push_back(MakeId(f.arena, "b"));
  inner->elements.push_back(MakeId(f.arena, "c"));

  auto* outer = f.arena.Create<Expr>();
  outer->kind = ExprKind::kConcatenation;
  outer->elements.push_back(MakeId(f.arena, "a"));
  outer->elements.push_back(inner);

  auto result = EvalExpr(outer, f.ctx, f.arena);
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

TEST(Eval, FunctionCallAsOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int result;\n"
      "  initial result = add(10, 20);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(Eval, ParameterReferenceAsOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int WIDTH = 42;\n"
      "  int x;\n"
      "  initial x = WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Eval, BitSelectAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic b;\n"
      "  initial begin a = 8'hA5; b = a[7]; end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 1u);
}

TEST(Eval, PartSelectAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin a = 8'hA5; b = a[3:0]; end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 0x5u);
}

TEST(Eval, UnpackedArrayElementAsOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  int arr[4];\n"
      "  int x;\n"
      "  initial begin arr[2] = 42; x = arr[2]; end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 42u);
}

TEST(Eval, NetReferenceUsesAllBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  wire [31:0] w;\n"
      "  assign w = 32'hDEADBEEF;\n"
      "endmodule\n",
      "w");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

}  // namespace
