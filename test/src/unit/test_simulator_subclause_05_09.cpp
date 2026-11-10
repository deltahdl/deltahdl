#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static std::string ElemChar(SimFixture& f, const std::string& name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return "";
  auto val = static_cast<char>(v->value.ToUint64() & 0xFF);
  return std::string(1, val);
}

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

TEST(LexicalConventionSim, LongStringNoLimit) {
  auto v = RunAndGet(
      "module t;\n  bit [63:0] s;\n"
      "  initial s = \"ABCDEFGH\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142434445464748u);
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(ElemChar(f, "c3[0]"), "h");
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedLast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(ElemChar(f, "c3[11]"), "\n");
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedPadding) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f, "c3[12]");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

TEST(LexicalConventionSim, EscapedNewlineIsSingleByte) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] d;\n  initial d = \"\\n\";\nendmodule\n", "d");
  EXPECT_EQ(v, 0x0Au);
}

TEST(LexicalConventionSim, StringLiteralOperandIsUnsigned) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int i = -1;\n"
                      "  bit b;\n"
                      "  initial b = (\"\\xff\" > i);\n"
                      "endmodule\n",
                      "b"),
            0u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  bit b;\n"
                      "  initial b = (\"A\" > -1);\n"
                      "endmodule\n",
                      "b"),
            0u);
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] w;\n"
                      "  initial w = \"\\x80\" >>> 1;\n"
                      "endmodule\n",
                      "w"),
            0x0040u);
}

TEST(LexicalConventionSim, CastStringLiteralToPackedArrayExactWidth) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] x;\n  initial x = 16'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x4142u);
}

TEST(LexicalConventionSim, CastStringLiteralToPackedArrayTruncatesLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] x;\n  initial x = 8'(\"AB\");\nendmodule\n", "x");
  EXPECT_EQ(v, 0x42u);
}

TEST(LexicalConventionSim, CastStringLiteralToPackedArrayZeroFillsLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] x;\n  initial x = 24'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x004142u);
}

TEST(LexicalConventionSim, DisplayFormatLineContinuationJoinsTheLines) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[a\\\nb]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[ab]\n");
}

TEST(LexicalConventionSim, DisplayFormatTripleBackslashKeepsOneBackslash) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[a\\\\\\\nb]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[a\\b]\n");
}

TEST(LexicalConventionSim, DisplayFormatEscapedNewlineThenContinuation) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[x\\n\\\ny]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[x\ny]\n");
}

TEST(LexicalConventionSim, TripleQuotedDisplayFormatPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"\"\"plain\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "plain\n");
}

TEST(LexicalConventionSim, TripleQuotedDisplayFormatKeepsAnInnerQuote) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"\"\"[a \"b\"]\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[a \"b\"]\n");
}

TEST(LexicalConventionSim, TripleQuotedDisplayFormatWithADirectNewline) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"\"\"sat on a \"wall\".\n"
      "had a great fall. \"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "sat on a \"wall\".\nhad a great fall. \n");
}

TEST(LexicalConventionSim, TripleQuotedLiteralAfterAnotherPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $write(\"x\", \"\"\"a \"b\\\"\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xa \"b\"");
}

TEST(LexicalConventionSim, TripleQuotedMacroBodyPrintsItsText) {
  SimFixture f;
  auto out = PreprocessAndCapture(
      "`define MSG \"\"\"say \"hi\" now\"\"\"\n"
      "module t;\n"
      "  initial $display(`MSG);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "say \"hi\" now\n");
}

TEST(LexicalConventionSim, TripleQuotedMacroArgumentPrintsItsText) {
  SimFixture f;
  auto out = PreprocessAndCapture(
      "`define SHOW(s) $display(s)\n"
      "module t;\n"
      "  initial `SHOW(\"\"\"arg \"x\" here\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "arg \"x\" here\n");
}

TEST(LexicalConventionSim, StringLiteralUnderDecimalConversionIsItsInteger) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", \"\\n\", \"\\t\", \"A\", "
      "\"AB\", \"A\" + 0);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 9 65 16706 65\n");
}

TEST(LexicalConventionSim, EscapedStringLiteralUnderDecimalConversion) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"%0d %0d %0d\", \"\\\\\", \"\\\"\", \"\\a\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "92 34 7\n");
}

TEST(LexicalConventionSim, StringLiteralUnderStringConversionPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%s]\", \"abc\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[abc]\n");
}

TEST(LexicalConventionSim, StringLiteralUnderSwriteDecimalConversion) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s, \"%0d\", \"A\");\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "65\n");
}

TEST(LexicalConventionSim, ProceduralStringToUnpackedByteArrayLeftJustified) {
  SimFixture f;
  auto* c0 = RunAndFindVar(
      "module t;\n"
      "  byte c [0:2];\n"
      "  initial c = \"ab\";\n"
      "endmodule\n",
      f, "c[0]");
  ASSERT_NE(c0, nullptr);
  EXPECT_EQ(ElemChar(f, "c[0]"), "a");
  EXPECT_EQ(ElemChar(f, "c[1]"), "b");
  EXPECT_EQ(f.ctx.FindVariable("c[2]")->value.ToUint64(), 0u);
}

TEST(LexicalConventionSim, CastStringToUnpackedByteArrayTypeLeftJustified) {
  SimFixture f;
  auto* b0 = RunAndFindVar(
      "module t;\n"
      "  typedef byte b3_t [0:2];\n"
      "  b3_t b = b3_t'(\"ab\");\n"
      "  b3_t c;\n"
      "  initial c = b3_t'(\"ab\");\n"
      "endmodule\n",
      f, "b[0]");
  ASSERT_NE(b0, nullptr);
  EXPECT_EQ(ElemChar(f, "b[0]"), "a");
  EXPECT_EQ(ElemChar(f, "b[1]"), "b");
  EXPECT_EQ(f.ctx.FindVariable("b[2]")->value.ToUint64(), 0u);
  EXPECT_EQ(ElemChar(f, "c[0]"), "a");
  EXPECT_EQ(ElemChar(f, "c[1]"), "b");
  EXPECT_EQ(f.ctx.FindVariable("c[2]")->value.ToUint64(), 0u);
}

TEST(LexicalConventionSim, StringLiteralFillsARangeNotEndingAtZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
                       "  initial $display(\"%h %h\", stringvar[8:1],\n"
                       "                   stringvar[96:89]);\n"
                       "endmodule\n",
                       f),
            "0a 48\n");
}

TEST(LexicalConventionSim, StringLiteralFillsAPackedArrayOfBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [0:11] [7:0] stringvar = \"Hello world\\n\";\n"
                       "  bit [0:11] [7:0] p;\n"
                       "  initial begin\n"
                       "    p = \"Hello world\\n\";\n"
                       "    $display(\"%h %h %h %h %s\", stringvar[0],\n"
                       "             stringvar[11], p[0], p[11], p[6]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "48 0a 48 0a w\n");
}

TEST(LexicalConventionSim, ShortStringLiteralZeroFillsTheLeftElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [0:11] [7:0] hi = \"Hi\";\n"
                       "  initial $display(\"%h %h %h %h\", hi[0], hi[9],\n"
                       "                   hi[10], hi[11]);\n"
                       "endmodule\n",
                       f),
            "00 00 48 69\n");
}

TEST(LexicalConventionSim, LongStringLiteralDropsTheLeftCharacters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [0:1] [7:0] two = \"abc\";\n"
                       "  initial $display(\"%h %h\", two[0], two[1]);\n"
                       "endmodule\n",
                       f),
            "62 63\n");
}

TEST(LexicalConventionSim, StringLiteralInAWidthNotAMultipleOfEight) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [11:0] x = \"AB\";\n"
                       "  bit [19:0] y = \"AB\";\n"
                       "  initial $display(\"%h %h\", x, y);\n"
                       "endmodule\n",
                       f),
            "142 04142\n");
}

TEST(LexicalConventionSim, MultiLineTripleQuotedLiteralKeepsEveryNewline) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s;\n"
                       "  initial begin\n"
                       "    s = \"\"\"\n"
                       "one 'a' \"b\"\n"
                       "two\n"
                       "\"\"\";\n"
                       "    $display(\"%s|%0d\", s, s.len());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "\none 'a' \"b\"\ntwo\n|17\n");
}

TEST(LexicalConventionSim, TripleQuotedLiteralInAStringDeclaration) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  string s = \"\"\"a\n"
                 "b\"\"\";\n"
                 "  string j = \"\"\"x\\\n"
                 "y\"\"\";\n"
                 "  initial $display(\"%0d %0d %s\", s.len(), j.len(), j);\n"
                 "endmodule\n",
                 f),
      "3 2 xy\n");
}

TEST(LexicalConventionSim, StringLiteralBesideAStringOperandIsAString) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  string s, t;\n"
                 "  initial begin\n"
                 "    s = \"abc\";\n"
                 "    t = {s, \"x\"};\n"
                 "    $display(\"%s %0d %0d %0d %0d\", t, t.len(),\n"
                 "             s == \"abc\", \"abd\" == s, s != \"abd\");\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "abcx 4 1 0 1\n");
}

}  // namespace
