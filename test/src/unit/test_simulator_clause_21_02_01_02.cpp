#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, SystemTaskDisplay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(FormatArg, HexLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x0A);

  EXPECT_EQ(FormatArg(val, 'h'), "0a");
}

TEST(FormatArg, OctalLeadingZeros) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 5);

  EXPECT_EQ(FormatArg(val, 'o'), "005");
}

TEST(FormatArg, BinaryReturnsToString) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 4, 0b1010);
  EXPECT_EQ(FormatArg(val, 'b'), "1010");
}

// §21.2.1.2 (C3): a field width of zero selects the minimum width, with no
// leading fill. The auto-sized "%h" of a 32-bit value would show eight hex
// digits; "%0h" collapses to the significant digit alone.
TEST(SizeOfDisplayedData, ZeroWidthHexUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 10)};
  EXPECT_EQ(FormatDisplay("%0h", vals), "a");
}

// §21.2.1.2 (C3): the same minimum-width rule for the decimal radix.
TEST(SizeOfDisplayedData, ZeroWidthDecimalUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 10)};
  EXPECT_EQ(FormatDisplay("%0d", vals), "10");
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

// §21.2.1.2 (C1/C2): without an explicit width the non-decimal radices remain
// auto-sized to the bit width with their leading zeros intact, so a width
// override is a true opt-in rather than a change to the default rendering.
TEST(SizeOfDisplayedData, NoWidthKeepsAutoSizedHex) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 10)};
  EXPECT_EQ(FormatDisplay("%h", vals), "0000000a");
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

}  // namespace
