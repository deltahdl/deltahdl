#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(RealLiteralConstantSim, RealFixedPointDecimal) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2);
}

TEST(RealLiteralConstantSim, RealSmallFixedPoint) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

TEST(RealLiteralConstantSim, RealLargeFixedPoint) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 2394.26331;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 2394.26331);
}

TEST(RealLiteralConstantSim, RealScientificUpperE) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.2E12;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.2e12);
}

TEST(RealLiteralConstantSim, RealScientificLowerENeg) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.30e-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 1.30e-2);
}

TEST(RealLiteralConstantSim, RealScientificZeroExponent) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 0.1e-0;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 0.1);
}

TEST(RealLiteralConstantSim, RealIntegerScientific) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 23E10;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 23e10);
}

TEST(RealLiteralConstantSim, RealIntegerNegativeExponent) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 29E-2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 29e-2);
}

TEST(RealLiteralConstantSim, RealUnderscoreIgnored) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 236.123_763_e-12;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 236.123763e-12);
}

TEST(RealLiteralConstantSim, RealNegativeUnaryMinus) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = -1.5;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, -1.5);
}

TEST(RealLiteralConstantSim, RealExponentPositiveSign) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.0e+2;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 100.0);
}

TEST(RealLiteralConstantSim, RealIEEE754BitExact) {
  auto bits =
      RunAndGet("module t;\n  real x;\n  initial x = 1.0;\nendmodule\n", "x");
  uint64_t expected = 0x3FF0000000000000ULL;
  EXPECT_EQ(bits, expected);
}

TEST(RealLiteralConstantSim, RealArithmeticExpression) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 1.5 + 2.25;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 3.75);
}

TEST(RealLiteralConstantSim, RealVariablePreservesValue) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 3.14159265358979;\nendmodule\n",
      "x");
  EXPECT_DOUBLE_EQ(v, 3.14159265358979);
}

TEST(RealLiteralConstantSim, RealLargeScientific) {
  auto v = RunAndGetReal(
      "module t;\n  real x;\n  initial x = 39e8;\nendmodule\n", "x");
  EXPECT_DOUBLE_EQ(v, 39e8);
}

TEST(RealLiteralConstantSim, IEEE754ZeroBitExact) {
  auto bits =
      RunAndGet("module t;\n  real x;\n  initial x = 0.0;\nendmodule\n", "x");
  EXPECT_EQ(bits, 0ULL);
}

TEST(RealLiteralConstantSim, IEEE754NegativeBitExact) {
  auto bits =
      RunAndGet("module t;\n  real x;\n  initial x = -1.0;\nendmodule\n", "x");
  uint64_t expected = 0xBFF0000000000000ULL;
  EXPECT_EQ(bits, expected);
}

TEST(RealLiteralConstantSim, ScientificNotation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.5e3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 1500.0);
}

TEST(RealLiteralConstantSim, ScientificNegativeExp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 1.0e-2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 0.01);
}

TEST(RealLiteralConstantSim, RealLiteralEval) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(3.14);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 3.14, 1e-10);
}

TEST(RealLiteralConstantSim, RealLiteralZero) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(0.0);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_EQ(VecToDouble(result), 0.0);
}

TEST(RealLiteralConstantSim, RealLiteralNegative) {
  RealFixture f;
  auto* lit = f.MakeRealLiteral(-2.5);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), -2.5, 1e-10);
}

TEST(RealLiteralConstantSim, FixedPointBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 3.14);
}

TEST(RealLiteralConstantSim, ExpUppercase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real x;\n"
      "  initial x = 2.5E2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_DOUBLE_EQ(ToDouble(var), 250.0);
}
