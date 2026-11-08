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

TEST(RealLiteralConstantSim, ShortrealCastOfHalfEqualsTheRealHalf) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic a;\n"
      "  initial a = (shortreal'(0.5) == 0.5);\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(v, 1u);
}

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

struct NearestBinary64 {
  const char* literal;
  uint64_t bits;
};

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

TEST(RealLiteralConstantSim, ProceduralLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  real r;\n  initial r = ";
    src += c.literal;
    src += ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}

TEST(RealLiteralConstantSim, DeclarationLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  real r = ";
    src += c.literal;
    src += ";\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}

TEST(RealLiteralConstantSim, ParameterLiteralHoldsTheNearestBinary64) {
  for (const NearestBinary64& c : NearestBinary64Cases()) {
    std::string src = "module t;\n  parameter real P = ";
    src += c.literal;
    src += ";\n  real r;\n  initial r = P;\nendmodule\n";
    EXPECT_EQ(RunAndGet(src, "r"), c.bits) << c.literal;
  }
}
