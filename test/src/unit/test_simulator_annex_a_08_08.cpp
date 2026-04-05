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

TEST(StringLiteralSim, QuotedStringWidthPerCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"ABC\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x414243u);
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

}  // namespace
