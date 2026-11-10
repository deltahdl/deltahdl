#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

static int32_t AsInt(uint64_t v) {
  return static_cast<int32_t>(v & 0xFFFFFFFFu);
}

TEST(StringMethods, CompareEqualReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareLessThanReturnsNegative) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abd\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, CompareGreaterThanReturnsPositive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

TEST(StringMethods, CompareBothEmptyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareEmptyOrdersBeforeNonEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, ComparePrefixOrdersBeforeLonger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  string u = \"abcd\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, CompareLongerOrdersAfterPrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abcd\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_GT(AsInt(v), 0);
}

TEST(StringMethods, CompareIsCaseSensitive) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ABC\";\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_LT(AsInt(v), 0);
}

TEST(StringMethods, CompareWithSelfReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = (s.compare(s) == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, CompareAgainstStringLiteralArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = (s.compare(\"abc\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, CompareOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"ab\", \"c\"};\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaa\";\n"
      "  string u = \"xyz\";\n"
      "  int r;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    r = s.compare(u);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u = \"Hi\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"abc\";\n"
      "  string s = p;\n"
      "  string u = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareArgumentIsParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"abc\";\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare(p);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareArgumentIsConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int r;\n"
      "  initial r = s.compare({\"ab\", \"c\"});\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareOnLiteralWithNullEscapeStripped) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\\0world\";\n"
      "  string u = \"helloworld\";\n"
      "  int r;\n"
      "  initial r = s.compare(u);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(AsInt(v), 0);
}

TEST(StringMethods, CompareResultIsSignedWhereverItIsUsed) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = (s.compare(\"abd\") < 0) + 2 * (s.compare(\"abb\") > 0) "
      "+\n"
      "              4 * (s.compare(\"abc\") == 0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 7u);
}

TEST(StringCompareSim, CompareOrdersTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; string ps = \"pkg\"; endpackage\n"
                 "typedef struct { string s; } one_t;\n"
                 "class C; string cs = \"Class\"; endclass\n"
                 "module t;\n"
                 "  string hi, lo = \"a\";\n"
                 "  one_t o;\n"
                 "  C c = new;\n"
                 "  function string h(); return \"Help\"; endfunction\n"
                 "  initial begin\n"
                 "    o.s = \"one\"; hi = string'(8'hE9);\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d\",\n"
                 "      p::ps.compare(\"pkg\"), c.cs.compare(\"class\") < 0,\n"
                 "      o.s.compare(h()) > 0, h().compare(\"Hello\") > 0,\n"
                 "      hi.compare(lo) > 0, lo.compare(hi) < 0);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 1 1 1 1 1\n");
}

}  // namespace
