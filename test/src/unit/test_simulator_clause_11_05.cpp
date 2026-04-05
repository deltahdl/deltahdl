#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(Eval, VariableLookup) {
  ExprFixture f;
  auto* var = f.ctx.CreateVariable("myvar", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 123);

  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "myvar";
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 123u);
}

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
  auto* va = f.ctx.CreateVariable("hi", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* vb = f.ctx.CreateVariable("lo", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0x5);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "hi"));
  concat->elements.push_back(MakeId(f.arena, "lo"));

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

}  // namespace
