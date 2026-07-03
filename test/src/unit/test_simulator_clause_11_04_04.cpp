#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §11.4.4: a relational expression over known operands yields a definite
// single-bit result (1'b1 when true). Integer literals are self-contained, so
// this exercises the pure evaluation rule directly.
TEST(RelationalEval, KnownOperandsYieldDefiniteResult) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// §11.4.4: a false relation yields 1'b0 in exactly one bit.
TEST(RelationalEval, FalseResultIsSingleBit) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// -- C1: true/false results through the full pipeline, one per operator. ------

TEST(OperatorSim, BinaryLessThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 < 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 > 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterOrEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 >= 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryLessOrEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 <= 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, FalseRelationalResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 > 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// -- C2: an x or z bit anywhere in an operand forces a 1'bx result. -----------
// The x/z is produced by a real 4-state literal stored into a declared
// variable, then read back as a relational operand.

TEST(OperatorSim, RelationalXOperandYieldsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x00;\n"
      "    b = 4'b0100;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  // An x result is flagged by its unknown (bval) bit being set.
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, RelationalZOperandYieldsX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1000;\n"
      "    b = 4'b0z10;\n"
      "    r = (a > b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

// -- C3: an unsigned operand makes the comparison unsigned; a narrower operand
// is zero-extended to the wider width. --------------------------------------

TEST(OperatorSim, UnsignedUnequalWidthZeroExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 8'h10;\n"
      "    r = (a < b);\n"  // 15 < 16 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnsignedHighValueNotLessThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h01;\n"
      "    r = (a < b);\n"  // unsigned 255 < 1 -> false
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// A single unsigned operand forces the whole comparison to be unsigned, so a
// negative signed operand is read as its large unsigned bit pattern: 0xFF is
// 255, not -1, and 255 < 1 is false. A stray signed reading would yield 1.
TEST(OperatorSim, MixedSignedUnsignedUsesUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 8'h01;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// -- C4: both operands signed -> signed comparison; a narrower operand is
// sign-extended to the wider width. -----------------------------------------

TEST(OperatorSim, SignedUnequalWidthSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -2;\n"       // 4'b1110
      "    b = 8'sd5;\n"    // +5
      "    r = (a < b);\n"  // -2 < 5 -> true, requires sign-extending a
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, SignedNegativeLessThanPositive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 1;\n"
      "    r = (a < b);\n"  // -1 < 1 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, SignedPositiveGreaterThanNegative) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = -1;\n"
      "    r = (a > b);\n"  // 1 > -1 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// -- C5: a real operand forces the other operand to be converted to real and
// the comparison to be done between real values. ----------------------------

TEST(OperatorSim, RealOperandConvertsIntegerOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real ra;\n"
      "  int i;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    ra = 2.5;\n"
      "    i = 3;\n"
      "    r = (ra < i);\n"  // 2.5 < 3.0 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, RealComparisonFalseResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1.0;\n"
      "    b = 2.0;\n"
      "    r = (a >= b);\n"  // 1.0 >= 2.0 -> false
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// C5, mirror position: a real operand on the right still forces the integer
// left operand to be converted to a real value before comparing.
TEST(OperatorSim, RealOnRightConvertsLeftOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  real x;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    i = 3;\n"
      "    x = 2.5;\n"
      "    r = (i > x);\n"  // 3.0 > 2.5 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// -- §11.4.3.1 dependency, operand-type input forms. --------------------------

// A default-signed type (integer) used as a relational operand drives a signed
// comparison with no explicit `signed` keyword: the signedness comes from the
// type itself (11.4.3.1).
TEST(OperatorSim, IntegerOperandsCompareSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 1;\n"
      "    r = (a < b);\n"  // -1 < 1 -> true
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// Signed net operands (Table 11-7) are compared as two's-complement values. The
// operands are produced by continuous assignments driving the nets.
TEST(OperatorSim, SignedNetOperandsCompareSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire signed [7:0] a, b;\n"
      "  wire r;\n"
      "  assign a = -1;\n"
      "  assign b = 1;\n"
      "  assign r = (a < b);\n"  // -1 < 1 -> true
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// Unsigned net operands (Table 11-7) force an unsigned comparison, so a large
// bit pattern is not read as a negative value.
TEST(OperatorSim, UnsignedNetOperandsCompareUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] a, b;\n"
      "  wire r;\n"
      "  assign a = 8'hFF;\n"
      "  assign b = 8'h01;\n"
      "  assign r = (a < b);\n"  // 255 < 1 -> false
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

}  // namespace
