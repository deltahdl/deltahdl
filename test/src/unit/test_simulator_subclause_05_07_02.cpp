#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

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

// §5.7.2 (printed page 80): a cast converts a real literal to shortreal, so
// `shortreal'(0.5)` is the single-precision 0.5, which equals the real 0.5.
// The cast masked the double's bit pattern to 32 bits, an integer of no
// relation to the value, and the comparison was false.
TEST(RealLiteralConstantSim, ShortrealCastOfHalfEqualsTheRealHalf) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic a;\n"
      "  initial a = (shortreal'(0.5) == 0.5);\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(v, 1u);
}

// A shortreal initialized from the cast holds the single-precision value, so
// `h + 2.0` is 2.5; it held 0.
TEST(RealLiteralConstantSim, ShortrealFromCastAddsAsItsValue) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  shortreal h = shortreal'(0.5);\n"
      "  real c;\n"
      "  initial c = h + 2.0;\n"
      "endmodule\n",
      "c");
  EXPECT_DOUBLE_EQ(v, 2.5);
}

// 1.2 is not exact in single precision, so the sum is 3.7 to the precision a
// float carries and not to a double's; the pattern read as an integer gave
// 858993474.5.
TEST(RealLiteralConstantSim,
     ShortrealFromCastOfInexactValueAddsToSinglePrecision) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  shortreal s = shortreal'(1.2);\n"
      "  real sum;\n"
      "  initial sum = s + 2.5;\n"
      "endmodule\n",
      "sum");
  EXPECT_NEAR(v, 3.7, 1e-6);
  EXPECT_NE(v, 3.7);
}

// §6.12 makes shortreal a C float, so the cast narrows: the single-precision
// 0.1 widened back into a real is not the double 0.1, which discriminates a
// cast that kept the double.
TEST(RealLiteralConstantSim, ShortrealCastNarrowsToSinglePrecision) {
  auto v = RunAndGet(
      "module t;\n"
      "  real r = shortreal'(0.1);\n"
      "  logic e;\n"
      "  initial e = (r == 0.1);\n"
      "endmodule\n",
      "e");
  EXPECT_EQ(v, 0u);
}
