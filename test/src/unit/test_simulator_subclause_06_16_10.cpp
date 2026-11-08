#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, AtorealFraction) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"3.14\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 3.14, 0.0001);
}

TEST(StringMethods, AtorealIntegerString) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"42\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 42.0, 0.0001);
}

TEST(StringMethods, AtorealExponentNotation) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1.5e2\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 150.0, 0.0001);
}

TEST(StringMethods, AtorealNegativeExponent) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1e-3\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 0.001, 0.000001);
}

TEST(StringMethods, AtorealScansDigitSeparatingUnderscore) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"1_000.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 1000.5, 0.0001);
}

TEST(StringMethods, AtorealStopsAtNonConforming) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"2.5xyz\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

TEST(StringMethods, AtorealNegativeValue) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"-3.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, -3.5, 0.0001);
}

TEST(StringMethods, AtorealNoDigitsReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

TEST(StringMethods, AtorealEmptyStringReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

TEST(StringMethods, AtorealNonNumericKeywordReturnsZero) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"inf\";\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(d, 0.0);
}

TEST(StringMethods, AtorealFromConcatenation) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = {\"2\", \".\", \"5\"};\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

TEST(StringMethods, AtorealFromReassignment) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"0.0\";\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = \"6.25\";\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 6.25, 0.0001);
}

TEST(StringMethods, AtorealFromCast) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = string'(16'h3334);\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 34.0, 0.0001);
}

TEST(StringMethods, AtorealFromParameterString) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  parameter string p = \"7.5\";\n"
      "  string s = p;\n"
      "  real r;\n"
      "  initial r = s.atoreal();\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 7.5, 0.0001);
}

TEST(StringMethods, AtorealResultAsExpressionOperand) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s = \"2.5\";\n"
      "  real r;\n"
      "  initial r = s.atoreal() + 1.0;\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 3.5, 0.0001);
}

}  // namespace
