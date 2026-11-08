#include <gtest/gtest.h>

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

TEST(LexicalConventionSim, OctalConsumesAtMostThreeDigits) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\1011\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4131u);
}

TEST(LexicalConventionSim, HexConsumesAtMostTwoDigits) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\x411\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4131u);
}

TEST(LexicalConventionSim, XAfterACompleteOctalEscapeIsACharacter) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\101x\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4178u);
}

TEST(LexicalConventionSim, XAfterACompleteHexEscapeIsACharacter) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"\\x41x\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4178u);
}

TEST(LexicalConventionSim, DoubleBackslashBeforeNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C42u);
}

TEST(LexicalConventionSim, DoubleBackslashBeforeNewlinePreservesNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"A\\\\\nB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C0A42u);
}

TEST(LexicalConventionSim, TripleQuotedEscapedQuote) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"\\\"X\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x2258u);
}

TEST(LexicalConventionSim, TripleQuotedEscapedNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"\\nX\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x0A58u);
}

}  // namespace
