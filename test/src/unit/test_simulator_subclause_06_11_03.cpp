#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SignedAndUnsigned, DefaultSignedScalarsCarriedToSimulator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "  shortint s;\n"
      "  int i;\n"
      "  longint l;\n"
      "  integer ig;\n"
      "  initial begin b = 0; s = 0; i = 0; l = 0; ig = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.FindVariable("b")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("s")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("i")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("l")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("ig")->is_signed);
}

TEST(SignedAndUnsigned, DefaultUnsignedScalarsCarriedToSimulator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  time t0;\n"
      "  bit b0;\n"
      "  logic l0;\n"
      "  reg r0;\n"
      "  initial begin t0 = 0; b0 = 0; l0 = 0; r0 = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.FindVariable("t0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("b0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("l0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("r0")->is_signed);
}

TEST(SignedAndUnsigned, PackedArraysOfUnsignedTypesAreUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit   [7:0]  ba;\n"
      "  logic [15:0] la;\n"
      "  reg   [3:0]  ra;\n"
      "  initial begin ba = 0; la = 0; ra = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.FindVariable("ba")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("la")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("ra")->is_signed);
}

TEST(SignedAndUnsigned, DefaultSignedByteSignExtendsAtRuntime) {
  // byte defaults to signed, so widening its all-ones pattern to a wider
  // destination sign-extends. This observes the default-signedness rule via
  // its arithmetic consequence, not just the carried is_signed flag: an
  // unsigned byte would zero-extend to 0x00000000000000FF instead.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "  longint d;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    d = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_TRUE(b->is_signed);
  EXPECT_EQ(d->value.width, 64u);
  EXPECT_EQ(d->value.ToUint64(), 0xFFFFFFFFFFFFFFFFull);
}

TEST(SignedAndUnsigned, DefaultUnsignedPackedArrayZeroExtendsAtRuntime) {
  // bit (and its packed array) defaults to unsigned, so widening its all-ones
  // pattern zero-extends. Discriminates the default: a signed bit vector would
  // sign-extend to all ones instead.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "  longint d;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    d = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(d, nullptr);
  EXPECT_FALSE(b->is_signed);
  EXPECT_EQ(d->value.width, 64u);
  EXPECT_EQ(d->value.ToUint64(), 0x00000000000000FFull);
}

TEST(SignedAndUnsigned, ExplicitSignedOverrideObservedAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit signed [3:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 4'b1111;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("src");
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_TRUE(src->is_signed);
  EXPECT_EQ(dst->value.width, 32u);
  EXPECT_EQ(dst->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(SignedAndUnsigned, ExplicitUnsignedOverrideObservedAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned src;\n"
      "  longint dst;\n"
      "  initial begin\n"
      "    src = 32'hFFFFFFFF;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("src");
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_FALSE(src->is_signed);
  EXPECT_EQ(dst->value.width, 64u);
  EXPECT_EQ(dst->value.ToUint64(), 0x00000000FFFFFFFFull);
}

TEST(SignedAndUnsigned, DefaultSignedByteComparesAsSignedOperand) {
  // Expression-operand form: a default-signed byte holding an all-ones
  // pattern is a negative value, so a relational compare against zero takes
  // the signed path. If byte defaulted to unsigned the operand would be 255
  // and the comparison would be false, so result==1 pins the default.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    result = (a < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* a = f.ctx.FindVariable("a");
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(result, nullptr);
  EXPECT_TRUE(a->is_signed);
  EXPECT_EQ(result->value.ToUint64(), 1u);
}

TEST(SignedAndUnsigned, DefaultUnsignedVectorComparesAsUnsignedOperand) {
  // Expression-operand form: a default-unsigned bit vector holding an all-ones
  // pattern is a large positive value, so a relational compare against zero
  // takes the unsigned path and is true. Were bit signed by default the
  // operand would be -1 and the comparison false, so result==1 pins the
  // default.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "  int result;\n"
      "  initial begin\n"
      "    b = -1;\n"
      "    result = (b > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(result, nullptr);
  EXPECT_FALSE(b->is_signed);
  EXPECT_EQ(result->value.ToUint64(), 1u);
}

TEST(SignedAndUnsigned, DefaultSignedIntegerReturnValueSignExtends) {
  // integer defaults to signed, and a function's result carries the
  // signedness of its declared return type, so widening a -1 result to a
  // longint sign-extends. This observes the default through its arithmetic
  // consequence at the one place a return type declares it: an unsigned
  // integer return would zero-extend to 0x00000000FFFFFFFF instead.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint d;\n"
      "  function integer f();\n"
      "    return -1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    d = f();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.width, 64u);
  EXPECT_EQ(d->value.ToUint64(), 0xFFFFFFFFFFFFFFFFull);
}

// §6.11.3: "The data types byte, shortint, int, integer, and longint default
// to signed." A for-init declaration declares a variable like any other, so an
// int loop variable is signed and -1 < 3 holds. Created from its width alone it
// was unsigned, -1 stood as 4294967295, and the body ran no times at all.
//
// The loop variable is popped when the loop ends, so what the count reaches is
// what says it was signed; there is no variable left to read the flag off.
TEST(SignedAndUnsigned, ForInitIntLoopVariableIsSignedInAProceduralBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    for (int i = -1; i < 3; i = i + 1) count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("count")->value.ToUint64(), 4u);
}

// The same loop inside a subroutine body, which a separate site creates the
// variable at: a for in a function body is set up by ExecFuncForInits and one
// in a procedural block by CreateForInitVars, so a fix reaching one leaves the
// other.
TEST(SignedAndUnsigned, ForInitIntLoopVariableIsSignedInAFunctionBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer count;\n"
      "  function integer steps_from_minus_one;\n"
      "    integer n;\n"
      "    n = 0;\n"
      "    for (int i = -1; i < 3; i = i + 1) n = n + 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "  initial count = steps_from_minus_one();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("count")->value.ToUint64(), 4u);
}

// §6.11.3 again for the other half of the sentence: "The data types time, bit,
// reg, and logic default to unsigned, as do arrays of these types." A loop
// counting down from 8'hFF while it exceeds zero runs 255 times unsigned and no
// times at all signed, where 8'hFF is -1. Without this a fix that marked every
// loop variable signed would satisfy the two cases above.
TEST(SignedAndUnsigned, ForInitLogicVectorLoopVariableStaysUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    for (logic [7:0] i = 8'hFF; i > 0; i = i - 1) count = count + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("count")->value.ToUint64(), 255u);
}

}  // namespace
