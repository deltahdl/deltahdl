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

// §5.7.2: the IEEE 754 value of a real literal must survive regardless of the
// syntactic position it is written in. The other value tests place the literal
// on the right-hand side of a procedural assignment; this one drives it through
// the distinct variable-declaration-initializer lowering path and reads the
// resulting run-time value back.
TEST(RealLiteralConstantSim, RealDeclarationInitializerValue) {
  auto v = RunAndGetReal("module t;\n  real r = 6.25;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 6.25);
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
