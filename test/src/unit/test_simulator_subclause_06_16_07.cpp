#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

static int32_t AsInt(uint64_t v) {
  return static_cast<int32_t>(v & 0xFFFFFFFFu);
}

TEST(StringMethods, IcompareEqualSameCaseReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareEqualIgnoringCaseReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"Hello\";\n"
      "  string u = \"hello\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareMixedCaseEqualReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u = \"hEllO\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareLessThanReturnsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abd\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, IcompareGreaterThanReturnsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

TEST(StringMethods, IcompareCaseFoldedOrderingIsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"B\";\n"
      "  string u = \"a\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

TEST(StringMethods, IcompareCaseFoldedOrderingIsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"ABD\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, IcompareBothEmptyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareEmptyOrdersBeforeNonEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, IcomparePrefixOrdersBeforeLonger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"ABCD\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, IcompareLongerOrdersAfterPrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABCD\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

TEST(StringMethods, IcompareWithSelfReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"Hello\";\n"
      "  int n;\n"
      "  initial n = (s.icompare(s) == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, IcompareAgainstStringLiteralArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABC\";\n"
      "  int n;\n"
      "  initial n = (s.icompare(\"abc\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, IcompareOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"AB\", \"c\"};\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaa\";\n"
      "  string u = \"xyz\";\n"
      "  int r;\n"
      "  initial begin\n"
      "    s = \"XYZ\";\n"
      "    r = s.icompare(u);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u = \"HI\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ABC\";\n"
      "  string s = p;\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareArgumentIsParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ABC\";\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare(p);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareArgumentIsConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.icompare({\"AB\", \"c\"});\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareOnLiteralWithNullEscapeStripped) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HEL\\0LO\";\n"
      "  string u = \"hello\";\n"
      "  int r;\n"
      "  initial r = s.icompare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, IcompareResultIsSignedWhereverItIsUsed) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = (s.icompare(\"ABD\") < 0) + 2 * (s.icompare(\"ABB\") > 0) "
      "+\n"
      "              4 * (s.icompare(\"ABC\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 7u);
}

TEST(StringIcompareSim, IcompareFoldsTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; string ps = \"PkG\"; endpackage\n"
                 "typedef struct { int n; string s; } two_t;\n"
                 "class D; static string ds = \"DyN\"; endclass\n"
                 "module t;\n"
                 "  string u = \"_\", aa [string];\n"
                 "  two_t w;\n"
                 "  function string m(); return \"MiXeD\"; endfunction\n"
                 "  initial begin\n"
                 "    w.s = \"TWO\"; aa[\"k\"] = \"Assoc\";\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d %0d\",\n"
                 "      p::ps.icompare(\"pkg\"), D::ds.icompare(\"dyn\"),\n"
                 "      w.s.icompare(aa[\"k\"]) > 0, m().icompare(\"mixed\"),\n"
                 "      u.icompare(\"a\") < 0, u.icompare(\"A\") < 0,\n"
                 "      u.compare(\"A\") > 0);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 0 1 0 1 1 1\n");
}

}  // namespace
