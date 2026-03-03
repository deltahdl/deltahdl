// §11.4.3: Arithmetic operators

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Arithmetic) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 + 4", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("10 - 3", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("6 * 7", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("15 / 3", f)), 5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("17 % 5", f)), 2);
}

TEST(ConstEval, DivisionByZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 / 0", f)), std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 % 0", f)), std::nullopt);
}

TEST(ConstEval, Power) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f)), 1024);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 ** 0", f)), 1);
}

// § expression — binary operations in initial block elaborate
TEST(ElabA83, BinaryExprInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.8.6 Operators — Elaboration
// =============================================================================
// § unary_operator — all unary operators elaborate
TEST(ElabA86, UnaryPlusElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = +a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, UnaryMinusElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = -a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § binary_operator — arithmetic operators elaborate
TEST(ElabA86, BinaryAddElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 + 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryDivElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd20 / 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryModElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd17 % 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA86, BinaryPowerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 ** 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ---------------------------------------------------------------------------
// 24. always_comb with addition and subtraction.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombAddSub) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'd100;\n"
      "    b = 8'd37;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a - b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 63u);
}

// ---------------------------------------------------------------------------
// 27. always_comb with subtraction.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombSubtraction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always_comb y = a - b;\n"
      "  initial begin\n"
      "    a = 8'h50;\n"
      "    b = 8'h10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x40u);
}

// ---------------------------------------------------------------------------
// 28. always_comb with multiplication.
// ---------------------------------------------------------------------------
TEST(SimCh9b, AlwaysCombMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b, y;\n"
      "  always_comb y = a * b;\n"
      "  initial begin\n"
      "    a = 16'd7;\n"
      "    b = 16'd6;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 42u);
}

// ---------------------------------------------------------------------------
// 17. Blocking assignment with arithmetic operators (+, -, *, /).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignArithmeticOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r_add, r_sub, r_mul, r_div;\n"
      "  initial begin\n"
      "    r_add = 10 + 3;\n"
      "    r_sub = 10 - 3;\n"
      "    r_mul = 10 * 3;\n"
      "    r_div = 10 / 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_add = f.ctx.FindVariable("r_add");
  auto* r_sub = f.ctx.FindVariable("r_sub");
  auto* r_mul = f.ctx.FindVariable("r_mul");
  auto* r_div = f.ctx.FindVariable("r_div");
  ASSERT_NE(r_add, nullptr);
  ASSERT_NE(r_sub, nullptr);
  ASSERT_NE(r_mul, nullptr);
  ASSERT_NE(r_div, nullptr);
  EXPECT_EQ(r_add->value.ToUint64(), 13u);
  EXPECT_EQ(r_sub->value.ToUint64(), 7u);
  EXPECT_EQ(r_mul->value.ToUint64(), 30u);
  EXPECT_EQ(r_div->value.ToUint64(), 3u);
}

// ---------------------------------------------------------------------------
// 29. Blocking assignment with modulo operator (%).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignModulo) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 17 % 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // 17 % 5 = 2
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
