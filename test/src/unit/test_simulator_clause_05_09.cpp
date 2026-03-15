#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(LexicalConventionSim, SingleCharValue) {
  auto v =
      RunAndGet("module t;\n  byte c;\n  initial c = \"A\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(LexicalConventionSim, MultiCharValue) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"ABC\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x414243u);
}

TEST(LexicalConventionSim, ZeroPadLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"A\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0041u);
}

TEST(LexicalConventionSim, TruncateLeft) {
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"ABCD\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x44u);
}

TEST(LexicalConventionSim, TripleQuotedBasic) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(LexicalConventionSim, TripleQuotedNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(LexicalConventionSim, TripleQuotedEmbeddedQuote) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

TEST(LexicalConventionSim, LineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"AB\\\nCD\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

TEST(LexicalConventionSim, DoubleBackslashNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C42u);
}

TEST(LexicalConventionSim, TripleQuotedLineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"AB\\\nCD\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

TEST(LexicalConventionSim, EmptyStringValue) {
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0u);
}

TEST(LexicalConventionSim, ExactWidthMatch) {
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"Z\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x5Au);
}

TEST(LexicalConventionSim, LongStringNoLimit) {
  auto v = RunAndGet(
      "module t;\n  bit [63:0] s;\n"
      "  initial s = \"ABCDEFGH\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142434445464748u);
}

TEST(LexicalConventionSim, TripleQuotedMultiLineValue) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"AB\nC\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41420A43u);
}

}  // namespace
