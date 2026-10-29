#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

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

// One real literal and the binary64 bit pattern nearest its decimal value.
struct NearestBinary64 {
  const char* literal;
  uint64_t bits;
};

// §5.7.2 makes a real literal an IEEE 754 double, whose value is the binary64
// nearest the decimal it writes, ties to even: a decimal no binary64 holds
// exactly in each literal form, a value halfway between two (2**53 + 1), the
// subnormal range on both sides of half the smallest subnormal, and a value
// past the largest finite double, which rounds to infinity.
static std::vector<NearestBinary64> NearestBinary64Cases() {
  return {{"0.1", 0x3FB999999999999AULL},
          {"0.1_0", 0x3FB999999999999AULL},
          {"1E-1", 0x3FB999999999999AULL},
          {"100e-3", 0x3FB999999999999AULL},
          {"1.30e-2", 0x3F8A9FBE76C8B439ULL},
          {"1e-300", 0x01A56E1FC2F8F359ULL},
          {"9007199254740993.0", 0x4340000000000000ULL},
          {"9.007199254740993e15", 0x4340000000000000ULL},
          {"4.9e-324", 0x0000000000000001ULL},
          {"2.5e-324", 0x0000000000000001ULL},
          {"2.4e-324", 0x0000000000000000ULL},
          {"1e309", 0x7FF0000000000000ULL}};
}

// Each literal, assigned in a procedure, holds exactly its nearest binary64.
TEST(RealLiteralConstantSim, ProceduralLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  real r;\n  initial r = ";
    src += c.literal;
    src += ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}

// The same in a declaration's initializer.
TEST(RealLiteralConstantSim, DeclarationLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  real r = ";
    src += c.literal;
    src += ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}

// The same as a parameter's value, which the elaborator folds before the
// variable reads it.
TEST(RealLiteralConstantSim, ParameterLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  parameter real P = ";
    src += c.literal;
    src += ";\n  real r;\n  initial r = P;\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}
