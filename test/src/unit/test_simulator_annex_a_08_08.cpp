#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SimA88, QuotedStringPacksBigEndian) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(SimA88, TripleQuotedStringPacksBigEndian) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(SimA88, EscapeSeqAnyAsciiNewline) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\n\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(SimA88, EscapeSeqAnyAsciiTab) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\t\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x09u);
}

TEST(SimA88, EscapeSeqAnyAsciiBackslash) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\\\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x5Cu);
}

TEST(SimA88, EscapeSeqAnyAsciiDoubleQuote) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x22u);
}

TEST(SimA88, EscapeSeqOctalOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\7\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(SimA88, EscapeSeqOctalTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\77\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x3Fu);
}

TEST(SimA88, EscapeSeqOctalThreeDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\101\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimA88, EscapeSeqHexOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\xA\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(SimA88, EscapeSeqHexTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\x41\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimA88, TripleQuotedStringItemNewlineIsLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(SimA88, TripleQuotedStringItemDoubleQuoteIsLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

TEST(SimA88, TripleQuotedStringEscapeSeq) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\n\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(SimA88, TripleQuotedStringEscapeSeqOctal) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\101\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimA88, TripleQuotedStringEscapeSeqHex) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\x41\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimA88, QuotedStringWidthPerCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"ABC\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x414243u);
}

}
