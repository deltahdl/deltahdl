#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoDisplayWriteSim, DisplayAppendsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi\n");
}

TEST(IoDisplayWriteSim, WriteOmitsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi");
}

TEST(IoDisplayWriteSim, DisplayNoArgsPrintsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

TEST(IoDisplayWriteSim, WriteNoArgsPrintsNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
}

TEST(IoDisplayWriteSim, TrailingEmptyArgIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"a\", );\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a ");
}

TEST(IoDisplayWriteSim, LeadingEmptyArgIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(,\"d\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " d");
}

TEST(IoDisplayWriteSim, DoubledCommaIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"b\",,\"c\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "b c");
}

TEST(IoDisplayWriteSim, SingleCommaIsTwoSpaces) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(,);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "  ");
}

TEST(IoDisplayWriteSim, WhitespacePaddedEmptyArgIsSingleSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"x\" , , \"y\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x y");
}

TEST(IoDisplayWriteSim, ArgumentsRenderInListOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"foo\", \"bar\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "foobar");
}

TEST(IoDisplayWriteSim, DoubledPercentRendersOnePercent) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"50%% done\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "50% done");
}

TEST(IoDisplayWriteSim, DisplayEmptyParensPrintsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

TEST(IoDisplayWriteSim, WriteEmptyParensPrintsNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
}

TEST(IoDisplayWriteSim, DisplayRadixVariantAppendsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $displayh(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi\n");
}

TEST(IoDisplayWriteSim, WriteRadixVariantOmitsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $writeb(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi");
}

TEST(IoDisplayWriteSim, HierarchicalSpecifierConsumesNoArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"%m\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(out.empty());
  EXPECT_EQ(out.find('%'), std::string::npos);
}

TEST(IoDisplayWriteSim, LibrarySpecifierConsumesNoArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"%l\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(out.empty());
  EXPECT_EQ(out.find('%'), std::string::npos);
}

TEST(IoDisplayWriteSim, TabEscapeRendersTab) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"a\\tb\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a\tb");
}

TEST(IoDisplayWriteSim, OctalEscapeRendersByte) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\123\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "S");
}

TEST(IoDisplayWriteSim, HexEscapeRendersByte) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\x41\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A");
}

TEST(IoDisplayWriteSim, OctalEscapedPercentIsLiteral) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\045d\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "%d");
}

TEST(IoDisplayWriteSim, CombinedBackslashAndPercentEscapes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"\\\\\\t\\\\\\n\\\"%%\\123\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\\\t\\\n\"%S\n");
}

TEST(IoDisplayWriteSim, DisplaybAppendsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $displayb(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi\n");
}

TEST(IoDisplayWriteSim, DisplayoAppendsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $displayo(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi\n");
}

TEST(IoDisplayWriteSim, WriteoOmitsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $writeo(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi");
}

TEST(IoDisplayWriteSim, WritehOmitsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $writeh(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi");
}

TEST(IoDisplayWriteSim, ArgumentsBeyondATemplatesSpecifiersPrintInOrder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [7:0] w = 8'd77;\n"
                       "  logic [3:0] v = 5;\n"
                       "  string s = \"hello\", n = \"nm\";\n"
                       "  initial begin\n"
                       "    $display(\":\", w);\n"
                       "    $displayb(\":\", w);\n"
                       "    $displayo(\":\", w);\n"
                       "    $displayh(\":\", w);\n"
                       "    $display(s, \" \", w);\n"
                       "    $display(\":\", v);\n"
                       "    $display(v, \":\");\n"
                       "    $display(\"%s\", n, , \"x\");\n"
                       "    $display(\"v=%0d\", 1, 2, 3);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            ": 77\n:01001101\n:115\n:4d\nhello  77\n: 5\n 5:\nnm x\n"
            "v=1          2          3\n");
}

TEST(IoDisplayWriteSim, StringLiteralIsThePendingPercentSValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s = \"xy\", o;\n"
                       "  initial begin\n"
                       "    $display(\":%3s:\", \"a\");\n"
                       "    $display(\":%3s:\", \"abcdef\");\n"
                       "    $display(\":%0s:\", \"a\");\n"
                       "    $display(\":%5s:\", s);\n"
                       "    $swrite(o, \":%3s:\", \"a\");\n"
                       "    $display(o);\n"
                       "    $sformat(o, \":%3s:\", \"a\");\n"
                       "    $display(o);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            ":  a:\n:abcdef:\n:a:\n:   xy:\n:  a:\n:  a:\n");
}

TEST(IoDisplayWriteSim, LiteralWithMoreConversionsThanArgumentsIsReported) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int a = 5;\n"
      "  initial begin\n"
      "    $display(\"%0d %h\", a);\n"
      "    $display(\"next\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "more format specifications than arguments", 4,
                              "21.2.1"));
  EXPECT_NE(out.find("next"), std::string::npos);
}

TEST(IoDisplayWriteSim, ConversionsTakingNoArgumentAreNotCounted) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int a = 5;\n"
      "  initial $display(\"%0d %m %l %%\", a);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
