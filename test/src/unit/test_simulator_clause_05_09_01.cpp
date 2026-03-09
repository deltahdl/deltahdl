#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SimClause05, Cl5_9_1_EscapeNewline) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\n\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(SimClause05, Cl5_9_1_EscapeTab) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\t\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x09u);
}

TEST(SimClause05, Cl5_9_1_EscapeBackslash) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\\\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x5Cu);
}

TEST(SimClause05, Cl5_9_1_EscapeDoubleQuote) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\"\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x22u);
}

TEST(SimClause05, Cl5_9_1_EscapeVerticalTab) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\v\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Bu);
}

TEST(SimClause05, Cl5_9_1_EscapeFormFeed) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\f\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Cu);
}

TEST(SimClause05, Cl5_9_1_EscapeBell) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\a\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(SimClause05, Cl5_9_1_OctalThreeDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\101\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimClause05, Cl5_9_1_OctalOneDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\7\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

TEST(SimClause05, Cl5_9_1_HexTwoDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\x41\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(SimClause05, Cl5_9_1_HexOneDigit) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xA\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

TEST(SimClause05, Cl5_9_1_UnknownEscapeDropsBackslash) {
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\b\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x62u);
}

TEST(SimClause05, Cl5_9_1_MultipleEscapes) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"A\\nB\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x410A42u);
}

}  // namespace
