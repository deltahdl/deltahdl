#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StringLiteralPaddingSim, StringLiteralPaddedWithZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0x00000048656c6c6fULL);
  EXPECT_EQ(var->value.words[1].aval & 0xFFFF, 0x0000u);
}

TEST(StringLiteralPaddingSim, PaddingAffectsConcatComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StringLiteralPaddingSim, PaddingZerosMatchExplicitNulsInConcat) {
  // Positive twin of the LRM's failing example. Using the same 8*10-wide s1/s2,
  // the padded concatenation compares equal to a reconstruction that supplies
  // the padding zeros explicitly (40'd0 ahead of "Hello", 24'd0 ahead of
  // " world!"). The comparison and concatenation operators must not tell the
  // left-pad zeros apart from those explicit NUL bytes, so the result is true
  // -- the earlier comparison against "Hello world!" fails only because that
  // literal lacks the interior zeros, not because padding is treated specially.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == {40'd0, \"Hello\", 24'd0, \" world!\"});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, ExactWidthNoPadding) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, LeadingNulStringCharsMatchPadding) {
  // A string literal whose high-order characters are explicit NUL escapes packs
  // the same bits as a shorter literal that the assignment left-pads with
  // zeros. Equality must not tell the two sources of zero bytes apart.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*3:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"A\";\n"
      "    result = (s == \"\\0\\0A\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, PaddedConcatPreservesZeroBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*4:1] s1, s2;\n"
      "  bit [8*8:1] combined;\n"
      "  initial begin\n"
      "    s1 = \"AB\";\n"
      "    s2 = \"CD\";\n"
      "    combined = {s1, s2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("combined");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000414200004344ULL);
}

TEST(StringLiteralPaddingSim, PaddingAffectsInequalityComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*6:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hi\";\n"
      "    s2 = \"!!\";\n"
      "    result = ({s1, s2} != \"Hi!!\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, SingleCharPaddedInWideVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*8:1] s;\n"
      "  initial s = \"Z\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x5AULL);
}

TEST(StringLiteralPaddingSim, PaddedStringSelfCompare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"test\";\n"
      "    result = (s == s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, FourStateVectorPaddingMatchesNul) {
  // The rule admits 4-state operands too: a logic vector left-padded on a
  // string assignment holds known zero bits, and equality (running the 4-state
  // compare path) must not tell those padding zeros apart from explicit NUL
  // characters.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [8*3:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"A\";\n"
      "    result = (s == \"\\0\\0A\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StringLiteralPaddingSim, FourStateConcatPreservesPaddingZeros) {
  // Concatenation over 4-state (logic) operands carries the interior padding
  // zeros through unchanged, just as the 2-state path does -- the operator does
  // not strip or specially treat the zeros produced by the string assignment.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [8*4:1] s1, s2;\n"
      "  logic [8*8:1] combined;\n"
      "  initial begin\n"
      "    s1 = \"AB\";\n"
      "    s2 = \"CD\";\n"
      "    combined = {s1, s2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("combined");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0000414200004344ULL);
}

}  // namespace
