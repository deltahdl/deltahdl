#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, AtoiDecimal) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"42\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 42u);
}

TEST(StringMethods, AtohexLowercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1f\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

TEST(StringMethods, AtohexUppercaseDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1F\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

TEST(StringMethods, AtooctBasic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"77\";\n"
      "  int n;\n"
      "  initial n = s.atooct();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 63u);
}

TEST(StringMethods, AtobinBasic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1010\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 10u);
}

TEST(StringMethods, AtoiStopsAtNonDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"123xyz\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

TEST(StringMethods, AtohexStopsAtNonHexDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1fg2\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0x1fu);
}

TEST(StringMethods, AtooctStopsAtNonOctalDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"78\";\n"
      "  int n;\n"
      "  initial n = s.atooct();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 7u);
}

TEST(StringMethods, AtobinStopsAtNonBinaryDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"102\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 2u);
}

TEST(StringMethods, AtoiScansUnderscores) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_000\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1000u);
}

TEST(StringMethods, AtobinScansUnderscores) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_010\";\n"
      "  int n;\n"
      "  initial n = s.atobin();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 10u);
}

TEST(StringMethods, AtoiNoDigitsReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, AtohexNoDigitsReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"xyz\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, AtoiEmptyStringReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, AtoiDoesNotParseSign) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"-5\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, AtoiDoesNotParseSizedLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"8'd2\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 8u);
}

TEST(StringMethods, AtohexDoesNotParseBasePrefix) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"0x1f\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, AtoiFromConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = {\"1\", \"2\", \"3\"};\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

TEST(StringMethods, AtoiFromReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"0\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"255\";\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 255u);
}

TEST(StringMethods, AtoiFromCast) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = string'(16'h3132);\n"
      "    n = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 12u);
}

TEST(StringMethods, AtohexFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"ff\";\n"
      "  string s = p;\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 255u);
}

TEST(StringMethods, AtoiFromEscapedLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\\x34\\x35\";\n"
      "  int n;\n"
      "  initial n = s.atoi();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 45u);
}

TEST(StringMethods, AtoiResultAsExpressionOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"23\";\n"
      "  int n;\n"
      "  initial n = s.atoi() + 100;\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 123u);
}

TEST(StringMethods, AtohexTruncatesToThirtyTwoBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1_0000_0001\";\n"
      "  int n;\n"
      "  initial n = s.atohex();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringAtoiSim, ConversionsReadTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; string ps = \"77\"; endpackage\n"
                 "typedef struct { string s; int n; } st_t;\n"
                 "class K; string ks = \"ff\"; endclass\n"
                 "module t;\n"
                 "  string q [$], a = \"4294967297\", b = \"_1_2x\";\n"
                 "  st_t st;\n"
                 "  K k = new;\n"
                 "  initial begin\n"
                 "    q.push_back(\"101\"); st.s = \"17\";\n"
                 "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\",\n"
                 "      p::ps.atoi(), k.ks.atohex(), q[0].atobin(),\n"
                 "      st.s.atooct(), a.atoi(), b.atoi(), $bits(a.atoi()),\n"
                 "      type(a.atoi()) == type(integer));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "77 255 5 15 1 12 32 1\n");
}

TEST(StringAtoiSim, DISABLED_ConversionsReturnASignedInteger) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string d = \"4294967295\", h = \"1ffffffff\";\n"
                       "  string o = \"777777777777\";\n"
                       "  string b = \"11111111111111111111111111111110\";\n"
                       "  int i;\n"
                       "  initial begin\n"
                       "    i = h.atohex();\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d\", d.atoi(),\n"
                       "             d.atoi() < 0, i, o.atooct(), b.atobin(),\n"
                       "             b.atobin() + 0 < 0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-1 1 -1 -1 -2 1\n");
}

}  // namespace
