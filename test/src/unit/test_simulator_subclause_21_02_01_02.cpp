#include <gtest/gtest.h>

#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(SizeOfDisplayedData, DecimalPaddedWithLeadingSpaces) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "  5");
}

TEST(SizeOfDisplayedData, DecimalWiderThanFieldExpands) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 1234)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "1234");
}

TEST(SizeOfDisplayedData, HexPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%3h", vals), "005");
}

TEST(SizeOfDisplayedData, StringPaddedWithLeadingSpaces) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 0x61)};
  EXPECT_EQ(FormatDisplay("%3s", vals), "  a");
}

TEST(SizeOfDisplayedData, BinaryPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0b101)};
  EXPECT_EQ(FormatDisplay("%5b", vals), "00101");
}

TEST(SizeOfDisplayedData, ZeroWidthBinaryUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0b0010)};
  EXPECT_EQ(FormatDisplay("%0b", vals), "10");
}

TEST(SizeOfDisplayedData, OctalPaddedWithLeadingZeros) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 8)};
  EXPECT_EQ(FormatDisplay("%4o", vals), "0010");
}

TEST(SizeOfDisplayedData, OctalWidthZeroUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 8)};
  EXPECT_EQ(FormatDisplay("%0o", vals), "10");
}

TEST(SizeOfDisplayedData, MultiDigitFieldWidthIsParsed) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 5)};
  EXPECT_EQ(FormatDisplay("%10d", vals), "         5");
}

TEST(SizeOfDisplayedData, ValueExactlyFillsField) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 100)};
  EXPECT_EQ(FormatDisplay("%3d", vals), "100");
}

TEST(SizeOfDisplayedData, ZeroValueBinaryUsesMinimumWidth) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 4, 0)};
  EXPECT_EQ(FormatDisplay("%0b", vals), "0");
}

TEST(SizeOfDisplayedData, StringWiderThanFieldExpands) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 48, 0x616263646566ULL)};
  EXPECT_EQ(FormatDisplay("%3s", vals), "abcdef");
}

TEST(SizeOfDisplayedData, HexWiderThanFieldExpands) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 32, 0x1234)};
  EXPECT_EQ(FormatDisplay("%3h", vals), "1234");
}

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

TEST(SizeOfDisplayedData, AutoSizedNinetySixBitDecimalRendersEveryWord) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [95:0] d;\n"
      "  initial begin\n"
      "    d = 96'h00000003_00000002_00000001;\n"
      "    $display(\":%d:\", d);\n"
      "    $display(\":%0d:\", d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            ":         55340232229718589441:\n"
            ":55340232229718589441:\n");
}

TEST(SizeOfDisplayedData, AutoSizedSignedNinetySixBitDecimalField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit signed [95:0] s;\n"
      "  initial begin\n"
      "    s = -1;\n"
      "    $display(\":%d:\", s);\n"
      "    s = -(96'sd1 << 70);\n"
      "    $display(\":%0d:\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            ":                            -1:\n"
            ":-1180591620717411303424:\n");
}

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

TEST(SizeOfDisplayedData, AutoSizedDecimalIntegerFunctionReturn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function integer add(integer a, integer b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\":%d:\", add(10, 20));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":         30:\n");
}

TEST(SizeOfDisplayedData, AutoSizedDecimalNegativeIntegerFunctionReturn) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function integer neg();\n"
      "    return -5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\":%d:\", neg());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":         -5:\n");
}

TEST(SizeOfDisplayedData,
     AutoSizedDecimalUnsignedFunctionReturnKeepsNarrowField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function logic [7:0] lo();\n"
      "    return 30;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\":%d:\", lo());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": 30:\n");
}

TEST(SizeOfDisplayedData,
     AutoSizedDecimalFunctionReturnMatchesLiteralExpression) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function integer add(integer a, integer b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\":%d::%d:\", add(2, 3), 2 + 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":          5::          5:\n");
}

TEST(SizeOfDisplayedData, AutoSizedDecimalIntegerFormalIsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function integer half(integer a);\n"
      "    return a / 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    $display(\":%d:\", half(-6));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":         -3:\n");
}

TEST(SizeOfDisplayedData, AutoSizedDecimalForInitLoopVariableIsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = -3; i < -2; i = i + 1) $display(\":%d:\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":         -3:\n");
}

TEST(SizeOfDisplayedData, ZeroWidthHexAndOctalKeepDigitsAboveBit63) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%0h %0o\", 80'h1_0000_0000_0000_00ff,\n"
      "                   80'h1_0000_0000_0000_0000);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "100000000000000ff 2000000000000000000000\n");
}

}  // namespace
