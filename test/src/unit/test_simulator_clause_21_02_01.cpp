#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// N1: $display appends a trailing newline to its output.
TEST(IoDisplayWriteSim, DisplayAppendsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi\n");
}

// N1: $write emits the same text but without a trailing newline.
TEST(IoDisplayWriteSim, WriteOmitsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi");
}

// N6: $display invoked with no arguments prints just a newline.
TEST(IoDisplayWriteSim, DisplayNoArgsPrintsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

// N6: $write invoked with no arguments prints nothing at all.
TEST(IoDisplayWriteSim, WriteNoArgsPrintsNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
}

// N5: a trailing empty argument (a comma with nothing after it) renders as a
// single space.
TEST(IoDisplayWriteSim, TrailingEmptyArgIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"a\", );\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a ");
}

// N5: a leading empty argument renders as a single space (and must not crash).
TEST(IoDisplayWriteSim, LeadingEmptyArgIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(,\"d\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " d");
}

// N5: an empty argument between two literals renders as one space; this is the
// LRM's worked example reproduced for $write.
TEST(IoDisplayWriteSim, DoubledCommaIsSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"b\",,\"c\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "b c");
}

// N5: a single comma between the parentheses is two empty arguments, so it
// renders as two spaces.
TEST(IoDisplayWriteSim, SingleCommaIsTwoSpaces) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(,);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "  ");
}

// N5: the commas that delimit an empty argument may carry surrounding white
// space. That white space belongs to no argument, so a padded comma still
// denotes exactly one empty argument and emits exactly one space -- here the
// single gap between "x" and "y" rather than several.
TEST(IoDisplayWriteSim, WhitespacePaddedEmptyArgIsSingleSpace) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"x\" , , \"y\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x y");
}

// N2: arguments are rendered in the order they appear in the argument list.
// Two adjacent string literals exercise ordering without invoking any format
// specifier: the first literal must precede the second in the output.
TEST(IoDisplayWriteSim, ArgumentsRenderInListOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"foo\", \"bar\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "foobar");
}

// N4c: a doubled percent sign in a string literal is rendered as one literal
// percent sign and consumes no expression argument.
TEST(IoDisplayWriteSim, DoubledPercentRendersOnePercent) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"50%% done\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "50% done");
}

// N6 edge: a no-argument $display written with empty parentheses still prints
// just a newline, identically to the parenthesis-free form.
TEST(IoDisplayWriteSim, DisplayEmptyParensPrintsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\n");
}

// N6 edge: a no-argument $write written with empty parentheses prints nothing,
// just as the parenthesis-free form does.
TEST(IoDisplayWriteSim, WriteEmptyParensPrintsNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "");
}

// N1/B2: a radix-suffixed display task ($displayh here) is part of the display
// family, so it terminates its output with a newline.
TEST(IoDisplayWriteSim, DisplayRadixVariantAppendsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $displayh(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi\n");
}

// N1/B2: a radix-suffixed write task ($writeb here) is part of the write
// family, so it emits its output with no trailing newline.
TEST(IoDisplayWriteSim, WriteRadixVariantOmitsNewline) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $writeb(\"hi\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hi");
}

// N4b: %m is one of the three specifiers (with %l and %%) that do not draw a
// corresponding expression argument from the list. Invoked with no expression
// argument at all, the call still succeeds and the specifier is consumed --
// nothing of the literal "%m" survives into the output.
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

// N4b: %l likewise needs no corresponding expression argument; supplied with an
// empty argument list it is still substituted rather than echoed literally.
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

// N3a: a '\' escape inside a string-literal argument is interpreted per
// Table 5-1 of 5.9.1. The tab escape must render as an actual tab byte, not the
// literal letter 't' -- so the decoder is more than a bare "\n handler".
TEST(IoDisplayWriteSim, TabEscapeRendersTab) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"a\\tb\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a\tb");
}

// N3a: an octal '\ddd' escape (from 5.9.1's Table 5-1) selects the byte with
// that octal code. \123 is octal 0123 == 'S'.
TEST(IoDisplayWriteSim, OctalEscapeRendersByte) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\123\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "S");
}

// N3a: a hex '\xhh' escape selects the byte with that hex code. \x41 == 'A'.
TEST(IoDisplayWriteSim, HexEscapeRendersByte) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\x41\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "A");
}

// N3a: an octal escape that resolves to '%' (octal 045) must reach the output
// as a literal percent sign -- the byte is decoded as literal text and is not
// re-interpreted as the start of a format specification.
TEST(IoDisplayWriteSim, OctalEscapedPercentIsLiteral) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $write(\"\\045d\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "%d");
}

// N3a/N4c: the worked example from 21.2.1, combining the '\' escape (backslash,
// tab, newline, escaped quote and octal \123 == 'S') with the '%%' literal
// percent. $display terminates the whole thing with a trailing newline.
TEST(IoDisplayWriteSim, CombinedBackslashAndPercentEscapes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"\\\\\\t\\\\\\n\\\"%%\\123\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "\\\t\\\n\"%S\n");
}

// N1/B2: $displayb is a display-family name; like every $display* task it
// terminates its output with a newline. Its radix suffix affects only the
// default radix of unformatted expression arguments, never the newline.
TEST(IoDisplayWriteSim, DisplaybAppendsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $displayb(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi\n");
}

// N1/B2: $displayo is likewise a display-family name and appends a newline.
TEST(IoDisplayWriteSim, DisplayoAppendsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $displayo(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi\n");
}

// N1/B2: $writeo is a write-family name and emits no trailing newline.
TEST(IoDisplayWriteSim, WriteoOmitsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $writeo(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi");
}

// N1/B2: $writeh completes the eight-name enumeration at the runtime stage; as
// a write-family name it too omits the trailing newline.
TEST(IoDisplayWriteSim, WritehOmitsNewline) {
  SimFixture f;
  std::string out =
      RunCapture("module t;\n  initial $writeh(\"hi\");\nendmodule\n", f);
  EXPECT_EQ(out, "hi");
}

}  // namespace
