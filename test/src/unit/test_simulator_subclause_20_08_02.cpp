#include <gtest/gtest.h>

#include <cmath>
#include <cstdio>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string DisplayReal(const std::string& call, SimFixture& f) {
  return RunCapture(
      "module t;\n"
      "  initial $display(\"%g\", " +
          call +
          ");\n"
          "endmodule\n",
      f);
}

TEST(RealMath, LnMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$ln(1.0)", f), "0\n");
}

TEST(RealMath, Log10MatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$log10(1000.0)", f), "3\n");
}

TEST(RealMath, ExpMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$exp(1.0)", f), "2.71828\n");
}

TEST(RealMath, SqrtMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sqrt(2.25)", f), "1.5\n");
}

TEST(RealMath, PowMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$pow(2.0, 10.0)", f), "1024\n");
}

TEST(RealMath, FloorMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$floor(7.9)", f), "7\n");
}

TEST(RealMath, CeilMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$ceil(7.1)", f), "8\n");
}

TEST(RealMath, SinMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sin(1.0)", f), "0.841471\n");
}

TEST(RealMath, CosMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$cos(0.0)", f), "1\n");
}

TEST(RealMath, TanMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$tan(0.0)", f), "0\n");
}

TEST(RealMath, AsinMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$asin(1.0)", f), "1.5708\n");
}

TEST(RealMath, AcosMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$acos(1.0)", f), "0\n");
}

TEST(RealMath, AtanMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atan(0.0)", f), "0\n");
}

TEST(RealMath, Atan2MatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atan2(0.0, 1.0)", f), "0\n");
}

TEST(RealMath, HypotMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$hypot(3.0, 4.0)", f), "5\n");
}

TEST(RealMath, SinhMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sinh(0.0)", f), "0\n");
}

TEST(RealMath, CoshMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$cosh(0.0)", f), "1\n");
}

TEST(RealMath, TanhMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$tanh(0.5)", f), "0.462117\n");
}

TEST(RealMath, AsinhMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$asinh(0.0)", f), "0\n");
}

TEST(RealMath, AcoshMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$acosh(1.0)", f), "0\n");
}

TEST(RealMath, AtanhMatchesC) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atanh(0.5)", f), "0.549306\n");
}

TEST(RealMath, AcceptsRealVariableArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real r = 2.25;\n"
      "  initial $display(\"%g\", $sqrt(r));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.5\n");
}

TEST(RealMath, ReturnsRealResultType) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", $pow(2.0, 10.0));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1024\n");
}

TEST(RealMath, SqrtOfNegativeMatchesCNaN) {
  SimFixture f;
  char want[32] = {};
  std::snprintf(want, sizeof(want), "%g\n", std::sqrt(-1.0));
  EXPECT_EQ(DisplayReal("$sqrt(-1.0)", f), want);
}

TEST(RealMath, LnOfZeroMatchesCNegativeInfinity) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$ln(0.0)", f), "-inf\n");
}

TEST(RealMath, NegatedRealLiteralIsARealArgument) {
  SimFixture f;
  EXPECT_EQ(DisplayReal("$floor(-2.5)", f), "-3\n");
}

TEST(RealMath, AParameterInitializedByAMathFunctionHoldsItsValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = $sqrt(2.25);\n"
                       "  localparam int I = $rtoi($pow(3, 2));\n"
                       "  initial $display(\"%f %0d\", R, I);\n"
                       "endmodule\n",
                       f),
            "1.500000 9\n");
}

}  // namespace
