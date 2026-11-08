#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringLiteralPaddingSim, StringLiteralPaddedWithZeros) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0x00000048656c6c6fULL);
  EXPECT_EQ(var->value.words[1].aval & 0xFFFF, 0x0000u);
}

TEST(StringLiteralPaddingSim, PaddingAffectsConcatComparison) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StringLiteralPaddingSim, PaddingZerosMatchExplicitNulsInConcat) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == {40'd0, \"Hello\", 24'd0, \" world!\"});\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, ExactWidthNoPadding) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*5:1] s1;\n"
      "  bit [8*7:1] s2;\n"
      "  bit [8*12:1] combined;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    combined = {s1, s2};\n"
      "    result = (combined == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, LeadingNulStringCharsMatchPadding) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*3:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"A\";\n"
      "    result = (s == \"\\0\\0A\");\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, PaddedConcatPreservesZeroBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*4:1] s1, s2;\n"
      "  bit [8*8:1] combined;\n"
      "  initial begin\n"
      "    s1 = \"AB\";\n"
      "    s2 = \"CD\";\n"
      "    combined = {s1, s2};\n"
      "  end\n"
      "endmodule\n",
      f, "combined");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000414200004344ULL);
}

TEST(StringLiteralPaddingSim, PaddingAffectsInequalityComparison) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*6:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hi\";\n"
      "    s2 = \"!!\";\n"
      "    result = ({s1, s2} != \"Hi!!\");\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, SingleCharPaddedInWideVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*8:1] s;\n"
      "  initial s = \"Z\";\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x5AULL);
}

TEST(StringLiteralPaddingSim, PaddedStringSelfCompare) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"test\";\n"
      "    result = (s == s);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, FourStateVectorPaddingMatchesNul) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8*3:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"A\";\n"
      "    result = (s == \"\\0\\0A\");\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, FourStateConcatPreservesPaddingZeros) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8*4:1] s1, s2;\n"
      "  logic [8*8:1] combined;\n"
      "  initial begin\n"
      "    s1 = \"AB\";\n"
      "    s2 = \"CD\";\n"
      "    combined = {s1, s2};\n"
      "  end\n"
      "endmodule\n",
      f, "combined");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000414200004344ULL);
}

}  // namespace
