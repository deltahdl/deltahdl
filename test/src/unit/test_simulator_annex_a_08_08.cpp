#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringLiteralSim, QuotedStringPacksBigEndian) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(StringLiteralSim, TripleQuotedStringPacksBigEndian) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(StringLiteralSim, EscapeSeqAnyAsciiNewline) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\n\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(StringLiteralSim, EscapeSeqAnyAsciiTab) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\t\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x09u);
}

TEST(StringLiteralSim, EscapeSeqAnyAsciiBackslash) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\\\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x5Cu);
}

TEST(StringLiteralSim, EscapeSeqAnyAsciiDoubleQuote) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x22u);
}

TEST(StringLiteralSim, EscapeSeqOctalOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\7\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(StringLiteralSim, EscapeSeqOctalTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\77\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x3Fu);
}

TEST(StringLiteralSim, EscapeSeqOctalThreeDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\101\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(StringLiteralSim, EscapeSeqHexOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\xA\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(StringLiteralSim, EscapeSeqHexTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\x41\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(StringLiteralSim, TripleQuotedStringItemNewlineIsLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(StringLiteralSim, TripleQuotedStringItemDoubleQuoteIsLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

TEST(StringLiteralSim, TripleQuotedStringEscapeSeq) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\n\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(StringLiteralSim, TripleQuotedStringEscapeSeqOctal) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\101\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(StringLiteralSim, TripleQuotedStringEscapeSeqHex) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\x41\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(StringLiteralSim, EscapeSeqUnknownDropsBackslash) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\b\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x62u);
}

// Negative boundary of `\x one_to_two_digit_hex_number`: a `\x` with no hex
// digit following does not match the hex alternative, so it falls back to
// `\any_ASCII_character` and yields the literal 'x' (0x78).
TEST(StringLiteralSim, EscapeSeqHexNoDigitYieldsLiteralX) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\x\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x78u);
}

// Negative boundary of `\one_to_three_digit_octal_number`: '8' is not an octal
// digit, so `\8` does not match the octal alternative and falls back to
// `\any_ASCII_character`, yielding the literal '8' (0x38).
TEST(StringLiteralSim, EscapeSeqNonOctalDigitYieldsLiteralDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\8\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x38u);
}

}  // namespace
