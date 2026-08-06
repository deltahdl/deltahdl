#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(LexicalConventionSim, EscapeNewline) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\n\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(LexicalConventionSim, EscapeTab) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\t\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x09u);
}

TEST(LexicalConventionSim, EscapeBackslash) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\\\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x5Cu);
}

TEST(LexicalConventionSim, EscapeDoubleQuote) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\"\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x22u);
}

TEST(LexicalConventionSim, EscapeVerticalTab) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\v\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Bu);
}

TEST(LexicalConventionSim, EscapeFormFeed) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\f\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Cu);
}

TEST(LexicalConventionSim, EscapeBell) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\a\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(LexicalConventionSim, OctalThreeDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\101\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(LexicalConventionSim, OctalOneDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\7\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(LexicalConventionSim, HexTwoDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\x41\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(LexicalConventionSim, HexOneDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xA\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(LexicalConventionSim, UnknownEscapeDropsBackslash) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\b\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x62u);
}

TEST(LexicalConventionSim, MultipleEscapes) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"A\\nB\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(LexicalConventionSim, OctalTwoDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\77\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x3Fu);
}

TEST(LexicalConventionSim, OctalMaxValid) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\377\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0xFFu);
}

TEST(LexicalConventionSim, HexUpperCase) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xFF\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0xFFu);
}

// The hex digits of a \x escape are case-insensitive, so lowercase a-f decode
// to the same byte as their uppercase counterparts.
TEST(LexicalConventionSim, HexLowerCase) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xff\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0xFFu);
}

TEST(LexicalConventionSim, NullByteOctal) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\0\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x00u);
}

// An octal escape absorbs at most three digits, so a fourth octal digit stands
// as its own character: \1011 is the byte 0101 ('A') followed by a literal '1'.
TEST(LexicalConventionSim, OctalConsumesAtMostThreeDigits) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\1011\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4131u);
}

// A hex escape absorbs at most two digits, so a third hex digit stands alone:
// \x411 is the byte 0x41 ('A') followed by a literal '1'.
TEST(LexicalConventionSim, HexConsumesAtMostTwoDigits) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\x411\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4131u);
}

// x is a valid digit in a numeric literal (see 5.7) but is never a digit of an
// octal escape, so it terminates the run and remains a literal character:
// \1x is the byte 0x01 followed by 'x'.
TEST(LexicalConventionSim, OctalEscapeExcludesXDigit) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\1x\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0178u);
}

// Likewise x is never a digit of a hex escape, so \x1x is the byte 0x01
// followed by a literal 'x'.
TEST(LexicalConventionSim, HexEscapeExcludesXDigit) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\x1x\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0178u);
}

TEST(LexicalConventionSim, DoubleBackslashBeforeNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C42u);
}

// A double backslash immediately before a newline is the escape for one
// backslash, so the newline is NOT swallowed as a line continuation but stays
// in the string. A triple-quoted literal hosts the bare newline (which a quoted
// literal would reject): """A\\<newline>B""" yields A, backslash, newline, B.
// Contrast the case above where a third backslash consumes the newline.
TEST(LexicalConventionSim, DoubleBackslashBeforeNewlinePreservesNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"A\\\\\nB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C0A42u);
}

// A triple-quoted string literal accepts an unescaped " directly, yet the \"
// escape for that character is also honored inside it. Observing the byte value
// confirms the escape (0x22) is interpreted rather than passed through
// literally.
TEST(LexicalConventionSim, TripleQuotedEscapedQuote) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"\\\"X\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x2258u);
}

// Likewise a triple-quoted literal accepts an unescaped newline, but the \n
// escape remains valid inside it and yields the newline byte (0x0A).
TEST(LexicalConventionSim, TripleQuotedEscapedNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"\\nX\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x0A58u);
}

}  // namespace
