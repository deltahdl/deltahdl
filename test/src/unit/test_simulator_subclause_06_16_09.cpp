#include <gtest/gtest.h>

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

}  // namespace
