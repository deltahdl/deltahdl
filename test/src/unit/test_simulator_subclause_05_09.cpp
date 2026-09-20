#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

static std::string ElemChar(SimFixture& f, const std::string& name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return "";
  auto val = static_cast<char>(v->value.ToUint64() & 0xFF);
  return std::string(1, val);
}

// The run's output for `src` taken through the preprocessor first, for a case
// whose literal reaches the simulator through a macro body or argument.
static std::string PreprocessAndCapture(const std::string& src) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, {});
  auto preprocessed = pp.Preprocess(fid);
  auto fid2 = f.mgr.AddFile("<preprocessed>", preprocessed);
  Lexer lexer(f.mgr.FileContent(fid2), fid2, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(TopNameOf(cu));
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
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

// §5.9: an escaped character sequence in a string literal is a single 8-bit
// ASCII value. "\n" occupies exactly one byte (0x0A), so it fits an 8-bit
// target unchanged (the bit [7:0] d = "\n" example).
TEST(LexicalConventionSim, EscapedNewlineIsSingleByte) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] d;\n  initial d = \"\\n\";\nendmodule\n", "d");
  EXPECT_EQ(v, 0x0Au);
}

// §5.9: a string literal can be cast to a packed array type, following the same
// rules as assigning it. A width-16 cast of the two-character literal packs the
// bytes exactly.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayExactWidth) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] x;\n  initial x = 16'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x4142u);
}

// §5.9: casting a string literal to a narrower packed array right justifies and
// truncates on the left, exactly as the assignment rules require.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayTruncatesLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] x;\n  initial x = 8'(\"AB\");\nendmodule\n", "x");
  EXPECT_EQ(v, 0x42u);
}

// §5.9: casting a string literal to a wider packed array right justifies and
// zero-fills on the left.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayZeroFillsLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] x;\n  initial x = 24'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x004142u);
}

// §5.9 (printed page 80): a backslash immediately before a newline inside a
// quoted string is ignored with the newline, so a `$display` format string
// continued across a line prints as one line. The string variable initializer
// already dropped both; the format string's own escape decoder dropped the
// backslash and kept the newline, printing `[a` and `b]` on two lines.
TEST(LexicalConventionSim, DisplayFormatLineContinuationJoinsTheLines) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[a\\\nb]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[ab]\n");
}

// §5.9.1 (printed page 83): a double backslash before the newline is the
// escape for one backslash and no continuation, so the third backslash is what
// continues the line and the output carries the one backslash.
TEST(LexicalConventionSim, DisplayFormatTripleBackslashKeepsOneBackslash) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[a\\\\\\\nb]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[a\\b]\n");
}

// §5.9's Example 2: an escaped `\n` before the continuation is the one newline
// the output carries; the continuation's own newline is dropped, so no empty
// line stands between the two.
TEST(LexicalConventionSim, DisplayFormatEscapedNewlineThenContinuation) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[x\\n\\\ny]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[x\ny]\n");
}

// §5.9 (printed page 81): a triple-quoted string literal is the text between
// its triple quotes and in every other way the same literal as a quoted one,
// so as a `$display` format it prints that text. The format string's own
// decoder stripped one quote at each end and printed `""plain""`; the string
// variable initializer beside it was already right.
TEST(LexicalConventionSim, TripleQuotedDisplayFormatPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"\"\"plain\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "plain\n");
}

// §5.9 (printed page 81): a `"` stands directly inside a triple-quoted string,
// so the format prints it as a character of the text.
TEST(LexicalConventionSim, TripleQuotedDisplayFormatKeepsAnInnerQuote) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"\"\"[a \"b\"]\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[a \"b\"]\n");
}

// §5.9's Example 3 (printed page 81): a newline stands directly inside a
// triple-quoted string, so the format prints its two lines as they are
// written, the inner quotes with them.
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

// §21.2.1 (printed page 655): every string literal argument of `$write` is
// output literally, so a triple-quoted literal after another literal prints
// its text after the first's. The literal was split at its first inner `"`
// and printed `""a "b"""`. The `\"` is the escape a quoted string needs too,
// since a bare `"` before the closing `"""` would close the literal early.
TEST(LexicalConventionSim, TripleQuotedLiteralAfterAnotherPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $write(\"x\", \"\"\"a \"b\\\"\"\"\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xa \"b\"");
}

// §22.5.1 with §5.9: a triple-quoted literal as a macro's whole body reaches
// `$display` as the same literal and prints its text.
TEST(LexicalConventionSim, TripleQuotedMacroBodyPrintsItsText) {
  auto out = PreprocessAndCapture(
      "`define MSG \"\"\"say \"hi\" now\"\"\"\n"
      "module t;\n"
      "  initial $display(`MSG);\n"
      "endmodule\n");
  EXPECT_EQ(out, "say \"hi\" now\n");
}

// §22.5.1 with §5.9: a triple-quoted literal as a macro's actual argument is
// substituted whole, its inner `"` included, and prints its text.
TEST(LexicalConventionSim, TripleQuotedMacroArgumentPrintsItsText) {
  auto out = PreprocessAndCapture(
      "`define SHOW(s) $display(s)\n"
      "module t;\n"
      "  initial `SHOW(\"\"\"arg \"x\" here\"\"\");\n"
      "endmodule\n");
  EXPECT_EQ(out, "arg \"x\" here\n");
}

// §5.9 (printed page 81, last paragraph) with §21.2.1.1 (printed 656): a
// string literal used as an operand is the unsigned integer its 8-bit ASCII
// codes make, an escape sequence one code, and each conversion of a format
// takes the expression argument that follows it, a string literal being one.
// The display path took every string literal argument as a template of its
// own, so the five printed as their characters in place of `10 9 65 16706 65`.
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

// §5.9.1 Table 5-1 (printed page 83) with §5.9: an escape sequence in a string
// literal operand is one 8-bit value, so `\\`, `\"` and `\a` are 92, 34 and 7
// under a decimal conversion where the path printed the characters.
TEST(LexicalConventionSim, EscapedStringLiteralUnderDecimalConversion) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"%0d %0d %0d\", \"\\\\\", \"\\\"\", \"\\a\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "92 34 7\n");
}

// §21.2.1.1: a string literal under a `%s` conversion prints its characters,
// which is what the template-of-its-own reading also printed; the conversion
// is what takes it now, so it is pinned beside the decimal cases.
TEST(LexicalConventionSim, StringLiteralUnderStringConversionPrintsItsText) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%s]\", \"abc\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[abc]\n");
}

// §21.3.3 with §21.2.1.1: `$swrite` takes its arguments as `$write` does, so a
// string literal following a decimal conversion is that conversion's integer.
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

}  // namespace
