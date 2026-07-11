#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Compiles and runs a full module, capturing everything the run writes to
// stdout via $display. §21.3.3's behaviour depends on how the output variable
// is declared (a string vs. a fixed-width integral), so every case is driven
// from real declaration syntax through the whole pipeline rather than a
// synthetic system-call node.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §21.3.3: $swrite writes the formatted output into the variable named by its
// first argument. A string destination holds the full result.
TEST(StringFormatTaskSim, SwriteWritesToStringVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s, \"x=%0d y=%0d\", 7, 11);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x=7 y=11\n");
}

// §21.3.3 (cross-ref §21.3.2): the b/h/o suffix selects the default radix for a
// bare expression argument, exactly as $fwriteb/$fwriteh/$fwriteo do. Each
// operand is sized so the rendered width is predictable.
TEST(StringFormatTaskSim, SwriteSuffixSelectsRadix) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] h;\n"
      "  logic [7:0] o;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    h = 8'hab; o = 8'o17; b = 4'b1010;\n"
      "    $swriteh(s, h); $display(\"%s\", s);\n"
      "    $swriteo(s, o); $display(\"%s\", s);\n"
      "    $swriteb(s, b); $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ab\n017\n1010\n");
}

// §21.3.3: $sformat always treats its second argument as the format string and
// writes the formatted result into the first-argument variable.
TEST(StringFormatTaskSim, SformatUsesSecondArgAsFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"data is %0d\", 123);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "data is 123\n");
}

// §21.3.3: only the second argument of $sformat is a format string; a later
// string argument is emitted verbatim through %s and never re-interpreted as
// another format template.
TEST(StringFormatTaskSim, SformatLaterStringArgIsNotFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"tag=%s\", \"raw %d nope\");\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "tag=raw %d nope\n");
}

// §21.3.3: the format argument may itself be a string-typed expression whose
// content is interpreted as the formatting string, not only a string literal.
TEST(StringFormatTaskSim, SformatFormatArgFromStringVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"n=%0d\";\n"
      "    $sformat(s, fmt, 9);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=9\n");
}

// §21.3.3: $sformat supports every format specifier $display supports
// (§21.2.1.1). %c, exercised here, confirms the engine linkage beyond the
// %d/%s arms.
TEST(StringFormatTaskSim, SformatSupportsCharacterSpecifier) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"ch=%c\", 65);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ch=A\n");
}

// §21.3.3: the remaining arguments fill the specifiers in call order. A
// three-specifier format with mixed integer and string positions binds
// 1, "two", 3 left to right.
TEST(StringFormatTaskSim, SformatConsumesArgsInOrder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"a=%0d, b=%s, c=%0d\", 1, \"two\", 3);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=1, b=two, c=3\n");
}

// §21.3.3: $sformatf returns the formatted string as the function value rather
// than placing it into a first argument, so it can be used where a string value
// is valid -- here the right-hand side of an assignment.
TEST(StringFormatTaskSim, SformatfReturnsFormattedResult) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = $sformatf(\"val=%0d\", 42);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "val=42\n");
}

// §21.3.3: the output variable is assigned using the string-literal
// assignment-to-variable rules (§5.9). Into a fixed-width integral variable of
// exactly the string width, the leftmost character occupies the highest byte
// (left bound to right bound): "ABCD" -> 0x41424344.
TEST(StringFormatTaskSim, SwriteByteOrderingIntoExactWidthVector) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  initial begin\n"
      "    $swrite(v, \"ABCD\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "41424344\n");
}

// §21.3.3 / §5.9: a fixed-width integral destination narrower than the result
// is truncated from the left (dropping the earliest characters), keeping the
// low bits. "ABCD" (32 bits) into a 16-bit variable retains "CD" = 0x4344.
TEST(StringFormatTaskSim, SwriteTruncatesNarrowerDestination) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  initial begin\n"
      "    $swrite(v, \"ABCD\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4344\n");
}

// §21.3.3 / §5.9: a fixed-width integral destination wider than the result is
// right-justified and zero-padded on the left. "AB" (16 bits) into a 32-bit
// variable yields 0x00004142.
TEST(StringFormatTaskSim, SformatRightJustifiesWiderDestination) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  initial begin\n"
      "    $sformat(v, \"AB\");\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "00004142\n");
}

// §21.3.3: if too few or too many arguments are supplied for the format
// specifiers, the application shall issue a warning and continue execution.
// The run still completes and writes the partially-formatted result.
TEST(StringFormatTaskSim, SformatArgCountMismatchWarnsAndContinues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"a=%0d b=%0d\", 1);\n"
      "    $display(\"done %s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
  // Execution continues: the $display after the warned call still runs.
  EXPECT_NE(out.find("done "), std::string::npos);
}

// §21.3.3: the output variable may be an unpacked array of byte. The resulting
// string's characters are stored from the array's left bound to its right bound
// -- for an ascending [0:3] range, character 0 ("A") lands in b[0] and the last
// character ("D") in b[3]. Read back with bare $display, which renders an
// unpacked byte array as its character string.
TEST(StringFormatTaskSim, SwriteIntoUnpackedByteArrayLeftToRight) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [0:3];\n"
      "  initial begin\n"
      "    $swrite(b, \"ABCD\");\n"
      "    $display(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ABCD\n");
}

// §21.3.3: $sformat likewise writes its formatted result into an unpacked
// byte-array destination. A result shorter than the array leaves the trailing
// elements cleared, so the rendered string is just the written characters.
TEST(StringFormatTaskSim, SformatIntoUnpackedByteArrayPadsRemainder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [0:3];\n"
      "  initial begin\n"
      "    $sformat(b, \"v%0d\", 7);\n"
      "    $display(b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "v7\n");
}

// §21.3.3 N1: the unsuffixed $swrite inherits the $fwrite rendering of a bare
// expression argument (no embedded format string) -- an unformatted integer
// renders in decimal. This is the default-radix arm, distinct from the b/h/o
// suffix arms exercised above.
TEST(StringFormatTaskSim, SwriteBareExpressionRendersDecimal) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'd255;\n"
      "    $swrite(s, v);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "255\n");
}

// §21.3.3 N4: for a descending [3:0] byte-array declaration, left-bound to
// right-bound ordering still places the leftmost character in the left-bound
// (highest-index) element. So b[3]='A' and b[0]='D'; reading the elements in
// ascending index order therefore yields "DCBA", distinguishing declared-order
// distribution from naive index-order distribution.
TEST(StringFormatTaskSim, SwriteIntoDescendingUnpackedByteArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte b [3:0];\n"
      "  initial begin\n"
      "    $swrite(b, \"ABCD\");\n"
      "    $display(\"%c%c%c%c\", b[0], b[1], b[2], b[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "DCBA\n");
}

// §21.3.3 N7: the format argument may be an expression of integral type whose
// packed bytes encode the formatting string -- not only a string literal or a
// string-typed variable. A logic vector holding the characters is decoded back
// into the template and drives the specifiers.
TEST(StringFormatTaskSim, SformatFormatArgFromIntegralExpression) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [39:0] fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"n=%0d\";\n"
      "    $sformat(s, fmt, 5);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "n=5\n");
}

// §21.3.3 N7: the format argument may be an unpacked array of byte, whose
// characters (left bound to right bound) are interpreted as the formatting
// string. The array is built from real element assignments and consumed as the
// second argument of $sformat; its reconstructed template "%0d!" then formats
// the trailing value.
TEST(StringFormatTaskSim, SformatFormatArgFromByteArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  byte fmt [0:3];\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt[0] = \"%\"; fmt[1] = \"0\"; fmt[2] = \"d\"; fmt[3] = \"!\";\n"
      "    $sformat(s, fmt, 5);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5!\n");
}

// §21.3.3 N9 (too-many branch): supplying more arguments than the format
// specifiers consume is also a mismatch -- the application shall warn and
// continue, writing the partially-formatted result. This is the opposite arm of
// the too-few case above.
TEST(StringFormatTaskSim, SformatTooManyArgsWarnsAndContinues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"only=%0d\", 1, 2, 3);\n"
      "    $display(\"done %s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
  EXPECT_NE(out.find("done only=1"), std::string::npos);
}

// §21.3.3 N12: $sformatf yields the formatted string as its function value, so
// it is valid anywhere a string value is -- including directly as an argument
// expression, not only as an assignment right-hand side. Used inline as a %s
// argument to $display, its result renders without an intermediate variable.
TEST(StringFormatTaskSim, SformatfUsableAsExpressionArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%s\", $sformatf(\"val=%0d\", 42));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "val=42\n");
}

}  // namespace
