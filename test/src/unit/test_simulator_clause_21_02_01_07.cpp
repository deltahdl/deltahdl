#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// §21.2.1.7 String format. The %s specifier prints ASCII codes as characters:
// the argument is read as a sequence of 8-bit groups, each group one
// character. A variable argument is right-justified (rightmost bit is the LSB
// of the last character), leading zeros are never printed, and no termination
// character is appended. The argument may also have a string type or be an
// unpacked array of byte, whose characters run from the left bound of the
// declaration to the right bound. These tests drive the whole pipeline: the
// argument is declared and assigned in real source, $display/$write hand it to
// the formatter, and the printed text is captured end to end.

namespace {

std::string RunSim(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  return testing::internal::GetCapturedStdout();
}

// §21.2.1.7 C1: %s prints the argument's ASCII codes as characters, 8 bits
// per character. A 16-bit variable holding 0x4869 renders as "Hi".
TEST(StringFormat, PrintsAsciiCodesAsCharacters) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'h4869;\n"
      "    $display(\"%s\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hi\n");
}

// §21.2.1.7 C1 (position): the same rendering applies under $write, which
// appends no newline, and Table 21-1 admits the uppercase %S spelling.
TEST(StringFormat, WriteTaskAndUppercaseSpelling) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v = 16'h4869;\n"
      "  initial $write(\"%S\", v);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hi");
}

// §21.2.1.7 C1 (position): a declaration initializer produces the value the
// same way a procedural assignment does; a string literal stored into a
// packed variable right-justifies, so %s reproduces the original text.
TEST(StringFormat, DeclarationInitializerFromStringLiteral) {
  auto out = RunSim(
      "module t;\n"
      "  bit [39:0] v = \"Hello\";\n"
      "  initial $display(\"%s\", v);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hello\n");
}

// §21.2.1.7 C2 (shall): for each %s specification in the string, a
// corresponding argument follows in the argument list, consumed left to
// right. Two %s specifiers pull two distinct arguments.
TEST(StringFormat, EachSpecifierConsumesItsOwnArgument) {
  auto out = RunSim(
      "module t;\n"
      "  byte c1, c2;\n"
      "  initial begin\n"
      "    c1 = \"A\";\n"
      "    c2 = \"B\";\n"
      "    $display(\"%s-%s\", c1, c2);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "A-B\n");
}

// §21.2.1.7 C2 (shall, negative): a %s whose required argument is absent from
// the list contributes no characters rather than crashing or consuming an
// out-of-range value.
TEST(StringFormat, MissingArgumentContributesNothing) {
  auto out = RunSim(
      "module t;\n"
      "  initial $display(\"[%s]\");\n"
      "endmodule\n");
  EXPECT_EQ(out, "[]\n");
}

// §21.2.1.7 C3 (should): a variable's value is right-justified so the
// rightmost bit is the LSB of the last character. A 12-bit value 0x341 has
// its low eight bits (0x41 = 'A') form the trailing character while the
// leftover top four bits (0x3) form the leading one -- the case that
// genuinely exercises justification, since byte-aligned widths map straight
// through.
TEST(StringFormat, ValueRightJustifiedWhenWidthNotAByteMultiple) {
  auto out = RunSim(
      "module t;\n"
      "  bit [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'h341;\n"
      "    $display(\"%s\", v);\n"
      "  end\n"
      "endmodule\n");
  std::string expected;
  expected.push_back(static_cast<char>(0x03));
  expected += "A\n";
  EXPECT_EQ(out, expected);
}

// §21.2.1.7 C4: leading zeros are never printed. A 24-bit value whose top
// byte is zero yields exactly the two nonzero characters, with no leading
// null and no termination character after them.
TEST(StringFormat, LeadingZeroBytesAreNotPrinted) {
  auto out = RunSim(
      "module t;\n"
      "  bit [23:0] v;\n"
      "  initial begin\n"
      "    v = 24'h004142;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[AB]\n");
}

// §21.2.1.7 C4 (boundary): a value of all zero bytes is entirely leading
// zeros, so nothing at all is printed for the specifier.
TEST(StringFormat, AllZeroValuePrintsNothing) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'h0000;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[]\n");
}

// §21.2.1.7 C4 (edge): only *leading* zeros are suppressed. A zero byte that
// sits between two nonzero characters is part of the value and passes through
// as a null character in the output.
TEST(StringFormat, EmbeddedZeroByteIsPreserved) {
  auto out = RunSim(
      "module t;\n"
      "  bit [23:0] v;\n"
      "  initial begin\n"
      "    v = 24'h410042;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  std::string expected = "[A";
  expected.push_back('\0');
  expected += "B]\n";
  EXPECT_EQ(out, expected);
}

// §21.2.1.7 C5: the argument may have a string type (§6.16). A string
// variable assigned procedurally round-trips through %s.
TEST(StringFormat, StringTypedArgument) {
  auto out = RunSim(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"Verilog\";\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "Verilog\n");
}

// §21.2.1.7 C5 (position): a string variable produced by a declaration
// initializer renders identically.
TEST(StringFormat, StringTypedArgumentFromInitializer) {
  auto out = RunSim(
      "module t;\n"
      "  string s = \"Init\";\n"
      "  initial $display(\"%s\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Init\n");
}

// §21.2.1.7 C6: the argument may be an unpacked array of byte (§7.4), whose
// character ordering runs from the left bound to the right bound. An
// ascending range [0:3] prints element 0 first.
TEST(StringFormat, ByteArrayAscendingRangePrintsLeftBoundFirst) {
  auto out = RunSim(
      "module t;\n"
      "  byte a [0:3];\n"
      "  initial begin\n"
      "    a[0] = \"A\";\n"
      "    a[1] = \"B\";\n"
      "    a[2] = \"C\";\n"
      "    a[3] = \"D\";\n"
      "    $display(\"%s\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "ABCD\n");
}

// §21.2.1.7 C6 (edge): for a descending range [3:0] the left bound is the
// highest index, so the walk runs from element 3 down to element 0 -- the
// case that distinguishes left-bound-first ordering from plain ascending
// index order.
TEST(StringFormat, ByteArrayDescendingRangePrintsLeftBoundFirst) {
  auto out = RunSim(
      "module t;\n"
      "  byte a [3:0];\n"
      "  initial begin\n"
      "    a[0] = \"a\";\n"
      "    a[1] = \"b\";\n"
      "    a[2] = \"c\";\n"
      "    a[3] = \"d\";\n"
      "    $display(\"%s\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "dcba\n");
}

// §21.2.1.7 C1 (operand type): a 4-state integer operand takes the same
// 8-bit-group reading as a 2-state bit vector. The 32-bit integer holding
// 0x4869 has two high zero bytes, which are leading and therefore absent
// from the output.
TEST(StringFormat, FourStateIntegerOperand) {
  auto out = RunSim(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 'h4869;\n"
      "    $display(\"[%s]\", i);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[Hi]\n");
}

// §21.2.1.7 C1 (position): the argument need not be a variable -- an
// expression operand (a concatenation of two byte variables) is read the
// same way. This is the non-variable counterpart of the right-justification
// wording, which speaks only of variable arguments.
TEST(StringFormat, ConcatenationExpressionOperand) {
  auto out = RunSim(
      "module t;\n"
      "  byte c1, c2;\n"
      "  initial begin\n"
      "    c1 = \"H\";\n"
      "    c2 = \"i\";\n"
      "    $display(\"[%s]\", {c1, c2});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[Hi]\n");
}

// §21.2.1.7 C1 (position): %s renders identically when the format string is
// consumed by $sformatf rather than a display task; the produced string is
// then observed through a plain $display of the string variable.
TEST(StringFormat, SformatfPositionRendersSameCharacters) {
  auto out = RunSim(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  string r;\n"
      "  initial begin\n"
      "    v = 16'h4F4B;\n"
      "    r = $sformatf(\"<%s>\", v);\n"
      "    $display(r);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "<OK>\n");
}

// §21.2.1.7 C6 (negative): %s admits an unpacked array only when its elements
// are of type byte. An unpacked array of int under %s is rejected with a
// run-time diagnostic and renders nothing.
TEST(StringFormat, NonByteUnpackedArrayIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1];\n"
      "  initial begin\n"
      "    a[0] = 65;\n"
      "    a[1] = 66;\n"
      "    $display(\"[%s]\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);  // the declaration and assignments are legal
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  auto out = testing::internal::GetCapturedStdout();
  EXPECT_TRUE(f.diag.HasErrors());  // the %s-on-int-array use is rejected
  EXPECT_EQ(out, "[]\n");           // the argument renders no characters
}

}  // namespace
