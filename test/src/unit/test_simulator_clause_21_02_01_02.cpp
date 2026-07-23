#include <iostream>
#include <sstream>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout. The automatic-sizing rules of
// §21.2.1.2 depend on the displayed expression's declared bit width and
// signedness, so these tests build that input from a real declaration and
// drive it through the full pipeline rather than hand-building a value.
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

// §21.2.1.2 (C4): a decimal value narrower than the field is left-padded with
// spaces. LRM example: "%3d" of 5 displays ":  5:".
TEST(SizeOfDisplayedData, DecimalPaddedWithLeadingSpaces) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "  5");
}

// §21.2.1.2 (C4): a value wider than the field expands to hold the converted
// result; no truncation occurs. LRM example: "%3d" of 1234 displays ":1234:".
TEST(SizeOfDisplayedData, DecimalWiderThanFieldExpands) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 1234)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "1234");
}

// §21.2.1.2 (C4): hexadecimal padding uses leading zeros rather than spaces.
// LRM example: "%3h" of 'h5 displays ":005:".
TEST(SizeOfDisplayedData, HexPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%3h", vals), "005");
}

// §21.2.1.2 (C4): string values, like decimal, are expanded with leading
// spaces. LRM example: "%3s" of "a" displays ":  a:".
TEST(SizeOfDisplayedData, StringPaddedWithLeadingSpaces) {
  Arena arena;
  // An 8-bit value carrying the single ASCII byte 0x61, which is "a".
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 0x61)};
  EXPECT_EQ(FormatDisplay("%3s", vals), "  a");
}

// §21.2.1.2 (C4): binary padding, like the other non-decimal radices, uses
// leading zeros.
TEST(SizeOfDisplayedData, BinaryPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0b101)};
  EXPECT_EQ(FormatDisplay("%5b", vals), "00101");
}

// §21.2.1.2 (C3): a width of zero on binary trims to the significant bits.
TEST(SizeOfDisplayedData, ZeroWidthBinaryUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0b0010)};
  EXPECT_EQ(FormatDisplay("%0b", vals), "10");
}

// §21.2.1.2 (C4): octal is one of the radices that pads with leading zeros.
// The octal rendering of 8 is "10"; in a four-column field it becomes "0010".
TEST(SizeOfDisplayedData, OctalPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 8)};
  EXPECT_EQ(FormatDisplay("%4o", vals), "0010");
}

// §21.2.1.2 (C3): a zero width on octal selects the minimum width, dropping the
// leading zeros that the auto-sized rendering would otherwise show.
TEST(SizeOfDisplayedData, OctalWidthZeroUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 8)};
  EXPECT_EQ(FormatDisplay("%0o", vals), "10");
}

// §21.2.1.2 (C3): the field width may run to several digits. A width of ten on
// a single-digit decimal value yields nine leading spaces.
TEST(SizeOfDisplayedData, MultiDigitFieldWidthIsParsed) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%10d", vals), "         5");
}

// §21.2.1.2 (C4) edge: when the converted value is exactly as wide as the
// field, it is neither padded nor expanded.
TEST(SizeOfDisplayedData, ValueExactlyFillsField) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 100)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "100");
}

// §21.2.1.2 (C3) edge: the minimum-width binary rendering of an all-zero value
// keeps a single digit rather than collapsing to an empty string.
TEST(SizeOfDisplayedData, ZeroValueBinaryUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0)};
  EXPECT_EQ(FormatDisplay("%0b", vals), "0");
}

// §21.2.1.2 (C4): string values, like decimal ones, expand past a too-small
// field instead of being truncated. Examples-table row: "%3s" of "abcdef"
// displays all six characters.
TEST(SizeOfDisplayedData, StringWiderThanFieldExpands) {
  Arena arena;
  // Six ASCII bytes packed MSB-first: "abcdef".
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 48, 0x616263646566ULL)};
  EXPECT_EQ(FormatDisplay("%3s", vals), "abcdef");
}

// §21.2.1.2 (C4): the zero-padded radices also expand rather than truncate.
// Examples-table row: "%3h" of 'h1234 displays all four hex digits.
TEST(SizeOfDisplayedData, HexWiderThanFieldExpands) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 0x1234)};
  EXPECT_EQ(FormatDisplay("%3h", vals), "1234");
}

// §21.2.1.2 (C1/C2): the LRM's printval example, driven end to end. A 12-bit
// expression auto-sizes to four decimal columns (its largest value is 4095)
// and three hex columns (fff); decimal replaces the suppressed leading zeros
// with spaces while hex keeps its leading zero. The %0 form of each collapses
// to the minimum width. The field comes from the declared width of r1, so the
// declaration is real source run through the whole pipeline.
TEST(SizeOfDisplayedData, AutoSizedTwelveBitDecimalAndHexFields) {
  SimFixture f;
  std::string out = RunCapture(
      "module printval;\n"
      "  logic [11:0] r1;\n"
      "  initial begin\n"
      "    r1 = 10;\n"
      "    $display(\":%d: :%h:\", r1, r1);\n"
      "    $display(\":%0d: :%0h:\", r1, r1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":  10: :00a:\n:10: :a:\n");
}

// §21.2.1.2 (C1): the Examples table's first row. A 32-bit unsigned value can
// reach 4294967295, so its automatic decimal field is ten columns and 10
// arrives right-justified behind eight spaces.
TEST(SizeOfDisplayedData, AutoSizedDecimalThirtyTwoBitField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  initial begin\n"
      "    v = 10;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":        10:\n");
}

// §21.2.1.2 (C1): the widest admitted operand -- a 64-bit unsigned value can
// reach a twenty-digit numeral, so its automatic decimal field is twenty
// columns, exercising the upper bound of the field computation.
TEST(SizeOfDisplayedData, AutoSizedSixtyFourBitDecimalField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [63:0] v;\n"
      "  initial begin\n"
      "    v = 10;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":                  10:\n");
}

// §21.2.1.2 (C1): the `int` keyword type is a signed 32-bit operand, so its
// automatic decimal field is eleven columns (ten digits plus the sign of the
// most negative value) -- one wider than the unsigned 32-bit field, which
// makes the signed/unsigned distinction observable from the declared type.
TEST(SizeOfDisplayedData, AutoSizedIntTypeUsesSignedField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = 42;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":         42:\n");
}

// §21.2.1.2 (C1): the sizing rules govern values written by the write family
// as well -- $write auto-sizes exactly as $display does, differing only in
// the absent trailing newline. This drives the other §21.2.1 task position.
TEST(SizeOfDisplayedData, WriteTaskAutoSizesLikeDisplay) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 5;\n"
      "    $write(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":  5:");
}

// §21.2.1.2 (C1): a signed expression's largest printable value is its most
// negative one, which carries a sign. An 8-bit signed field is therefore four
// columns (-128); both a positive and a negative value land right-justified
// in that same field. The signedness comes from the real declaration.
TEST(SizeOfDisplayedData, AutoSizedDecimalSignedCountsSignColumn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic signed [7:0] v;\n"
      "  initial begin\n"
      "    v = 10;\n"
      "    $display(\":%d:\", v);\n"
      "    v = -5;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":  10:\n:  -5:\n");
}

// §21.2.1.2 (C2): in the non-decimal radices the automatic sizing keeps every
// leading zero, driven from a real 8-bit declaration: two hex digits, three
// octal digits, eight binary digits.
TEST(SizeOfDisplayedData, AutoSizedOtherRadicesKeepLeadingZeros) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'h0a;\n"
      "    $display(\":%h: :%o: :%b:\", v, v, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":0a: :012: :00001010:\n");
}

// §21.2.1.2 (C1): a bare expression argument is also "sized automatically" --
// the default decimal rendering of §21.2.1.1 takes the same fixed-width field
// an explicit %d would, so an 8-bit value prints in three columns.
TEST(SizeOfDisplayedData, BareArgumentDefaultDecimalIsAutoSized) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    $display(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " 42\n");
}

// §21.2.1.2 (C1 x §21.2.1.3): a value carrying unknown bits still occupies the
// automatically sized decimal field -- the single status character of a 12-bit
// all-x value sits right-justified in the four-column field.
TEST(SizeOfDisplayedData, AutoSizedFieldHoldsUnknownStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:0] w;\n"
      "  initial $display(\":%d:\", w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":   x:\n");
}

// §21.2.1.2 (C3 negative): the inserted field width shall be a non-negative
// decimal integer constant. A C-style negative (left-justify) width is not
// part of the language; the specifier is not honored -- no left-justified
// rendering is produced and the malformed text passes through, flagging the
// misuse instead of silently inventing a meaning for it.
TEST(SizeOfDisplayedData, NegativeFieldWidthIsRejected) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 5;\n"
      "    $display(\"%-3d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out.find("5  "), std::string::npos);
  EXPECT_NE(out.find("%-"), std::string::npos);
}

}  // namespace
