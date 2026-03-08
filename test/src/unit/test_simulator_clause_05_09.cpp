#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SimClause05, Cl5_9_SingleCharValue) {
  auto v =
      RunAndGet("module t;\n  byte c;\n  initial c = \"A\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimClause05, Cl5_9_MultiCharValue) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"ABC\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x414243u);
}

TEST(SimClause05, Cl5_9_ZeroPadLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"A\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0041u);
}

TEST(SimClause05, Cl5_9_TruncateLeft) {
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"ABCD\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x44u);
}

TEST(SimClause05, Cl5_9_TripleQuotedBasic) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(SimClause05, Cl5_9_TripleQuotedNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(SimClause05, Cl5_9_TripleQuotedEmbeddedQuote) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

TEST(SimClause05, Cl5_9_LineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"AB\\\nCD\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

TEST(SimClause05, Cl5_9_DoubleBackslashNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C42u);
}

TEST(SimClause05, Cl5_9_TripleQuotedLineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"AB\\\nCD\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

}
