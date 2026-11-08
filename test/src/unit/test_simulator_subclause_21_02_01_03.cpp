#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UnknownAndHighImpedance, DecimalAllUnknownIsLowercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxxxx;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": x:\n");
}

TEST(UnknownAndHighImpedance, DecimalAllHighZIsLowercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": z:\n");
}

TEST(UnknownAndHighImpedance, DecimalSomeUnknownIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01x0;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n");
}

TEST(UnknownAndHighImpedance, DecimalSomeHighZIsUppercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z0;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": Z:\n");
}

TEST(UnknownAndHighImpedance, DecimalMixedHighZAndUnknownIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxz01;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n");
}

TEST(UnknownAndHighImpedance, DecimalStatusCharRightJustifiedInField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'bx;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":   x:\n");
}

TEST(UnknownAndHighImpedance, DecimalLrmExampleSingleBitUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", 1'bx);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

TEST(UnknownAndHighImpedance, HexLrmExampleExtendedUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%h\", 14'bx01010);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xxXa\n");
}

TEST(UnknownAndHighImpedance, HexOctalLrmExampleMixedGroups) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%h %o\", 12'b001xxx101x01, 12'b001xxx101x01);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "XXX 1x5X\n");
}

TEST(UnknownAndHighImpedance, HexAllHighZGroupIsLowercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z\n");
}

TEST(UnknownAndHighImpedance, HexSomeHighZGroupIsUppercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z1;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Z\n");
}

TEST(UnknownAndHighImpedance, HexMixedHighZAndUnknownGroupIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bx1z1;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "X\n");
}

TEST(UnknownAndHighImpedance, OctalHighZGroupLadder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [8:0] v;\n"
      "  initial begin\n"
      "    v = 9'bzzz1z0xz1;\n"
      "    $display(\"%o\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "zZX\n");
}

TEST(UnknownAndHighImpedance, BinaryPrintsEachBitWithXAndZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1x0z;\n"
      "    $display(\"%b\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1x0z\n");
}

TEST(UnknownAndHighImpedance, DecimalKnownValueShowsNumeral) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1010;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":10:\n");
}

TEST(UnknownAndHighImpedance, UninitializedVariableDisplaysAllUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial $display(\"%h\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx\n");
}

TEST(UnknownAndHighImpedance, UndrivenNetDisplaysHighZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  initial $display(\"%h\", w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z\n");
}

TEST(UnknownAndHighImpedance, TwoStateOperandNeverShowsStatusChars) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] b;\n"
      "  initial begin\n"
      "    b = 4'bx01z;\n"
      "    $display(\"%b\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0010\n");
}

TEST(UnknownAndHighImpedance, HexUnknownBitInUpperWordGroup) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [67:0] v;\n"
      "  initial begin\n"
      "    v = 68'b1x0000000000000000000000000000000000000000000000000000000"
      "0000001010;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "X000000000000000a\n");
}

TEST(UnknownAndHighImpedance, HexStatusCharSurvivesFieldWidth) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z1;\n"
      "    $display(\":%2h:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":0Z:\n");
}

TEST(UnknownAndHighImpedance, MinimumWidthKeepsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'bx;\n"
      "    $display(\":%0d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":x:\n");
}

TEST(UnknownAndHighImpedance, ExpressionResultUnknownShowsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", 1'b1 & 1'bx);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

TEST(UnknownAndHighImpedance, WriteTaskShowsDecimalStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $write(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": z:");
}

TEST(UnknownAndHighImpedance, BareArgumentDefaultDecimalShowsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxxxx;\n"
      "    $display(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " x\n");
}

TEST(UnknownAndHighImpedance, UppercaseSpecifiersFollowSameRules) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01x0;\n"
      "    $display(\":%D:\", v);\n"
      "    $display(\":%H:\", 14'bx01010);\n"
      "    $display(\":%O:\", 6'b01z101);\n"
      "    v = 4'b1x0z;\n"
      "    $display(\":%B:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n:xxXa:\n:Z5:\n:1x0z:\n");
}

TEST(UnknownAndHighImpedance, SignedIntegerTypeStatusCharInSignedField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 32'bx;\n"
      "    $display(\":%d:\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":          x:\n");
}

TEST(UnknownAndHighImpedance, TimeTypeStatusCharInWideField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  time tm;\n"
      "  initial begin\n"
      "    tm = 64'bx;\n"
      "    $display(\":%d:\", tm);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":                   x:\n");
}

TEST(UnknownAndHighImpedance, PackedStructOperandClassifiesLikeVector) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  struct packed { logic [1:0] hi; logic [1:0] lo; } s;\n"
      "  initial begin\n"
      "    s = 4'b1z0x;\n"
      "    $display(\":%b: :%h:\", s, s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":1z0x: :X:\n");
}

TEST(UnknownAndHighImpedance, TimeFieldWidthOverridesTheTimeformatMinimum) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\":%0t:%4t:%t:\", 12, 12, 12);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":12:  12:" + std::string(18, ' ') + "12:\n");
}

}  // namespace
