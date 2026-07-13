#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Arithmetic) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 + 4", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("10 - 3", f)), 7);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("6 * 7", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("15 / 3", f)), 5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("17 % 5", f)), 2);
}

TEST(ConstEval, DivisionByZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 / 0", f)), std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("5 % 0", f)), std::nullopt);
}

TEST(ConstEval, Power) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f)), 1024);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("3 ** 0", f)), 1);
}

TEST(ConstEval, ZeroPowerZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ** 0", f)), 1);
}

TEST(ConstEval, NegativeIntegerDivisionTruncatesTowardZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-7 / 2", f)), -3);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("7 / -2", f)), -3);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-7 % 2", f)), -1);
}

TEST(ConstEval, ZeroPowerNegative) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ** -1", f)), std::nullopt);
}

// Table 11-4: integral power with a negative exponent. For a base whose
// magnitude exceeds one the truncated reciprocal is zero; a base of one stays
// one; a base of negative one alternates with the parity of the exponent.
TEST(ConstEval, IntegralPowerNegativeExponentTable) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** -1", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-2) ** -1", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ** -5", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-1) ** -3", f)), -1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-1) ** -2", f)), 1);
}

// Table 11-4: integral power with a positive exponent and a negative base.
// A base below negative one raises normally; a base of negative one alternates
// between negative one and one with the parity of the exponent.
TEST(ConstEval, IntegralPowerNegativeBasePositiveExponent) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-2) ** 3", f)), -8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-1) ** 3", f)), -1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-1) ** 2", f)), 1);
}

TEST(OperatorElaboration, UnaryPlusElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = +a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryMinusElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, a;\n"
      "  initial x = -a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinarySubElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd30 - 8'd12;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryMulElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd7 * 8'd6;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryAddElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 + 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryDivElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd20 / 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryModElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd17 % 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryPowerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 ** 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.3 in a constant expression: parameter operands take a different
// evaluation path than literals (the elaborator must resolve the parameter
// reference to its value first). Once resolved, integer division truncates the
// negative quotient toward zero (-3, not -4) and modulus carries the sign of
// the first operand (-1). The operands are produced by real parameter
// declarations and the folded localparam values are read back after elaborate.
TEST(OperatorElaboration, ParameterOperandDivisionAndModulus) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = -7;\n"
      "  parameter int B = 2;\n"
      "  localparam int Q = A / B;\n"
      "  localparam int R = A % B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  bool saw_q = false, saw_r = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "Q") {
      saw_q = true;
      EXPECT_EQ(p.resolved_value, -3);
    }
    if (p.name == "R") {
      saw_r = true;
      EXPECT_EQ(p.resolved_value, -1);
    }
  }
  EXPECT_TRUE(saw_q);
  EXPECT_TRUE(saw_r);
}

// §11.4.3 in a constant expression: localparam operands are another admitted
// constant form. A power whose base and exponent are both localparams folds to
// 3 ** 4 == 81 during elaboration.
TEST(OperatorElaboration, LocalparamOperandPower) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int BASE = 3;\n"
      "  localparam int EXP = 4;\n"
      "  localparam int P = BASE ** EXP;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  bool saw_p = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "P") {
      saw_p = true;
      EXPECT_EQ(p.resolved_value, 81);
    }
  }
  EXPECT_TRUE(saw_p);
}

// §11.4.3 in a constant expression: a genvar is a constant operand (11.2.1).
// The loop's continuation is a multiplication over the genvar, i * i <= 9, true
// for i = 1, 2, 3 and false at i = 4, so the elaborator unrolls exactly three
// blocks. The resulting variable count observes the multiply applied to a
// genvar operand.
TEST(OperatorElaboration, GenvarOperandControlsGenerateUnroll) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i * i <= 9; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->variables.size(), 3u);
}

TEST(ConstEvalReal, SubtractReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("5.0 - 2.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 3.0);
}

TEST(ConstEvalReal, DivideReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("7.0 / 2.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 3.5);
}

TEST(ConstEvalReal, PowerReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("9.0 ** 0.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(val.value_or(0.0), 3.0, 1e-9);
}

TEST(ConstEvalReal, UnaryMinusOnReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("-3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(val.value_or(0.0), -3.14, 1e-6);
}

TEST(ConstEvalReal, BinaryAddReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.5 + 2.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 4.0);
}

TEST(ConstEvalReal, BinaryMulReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("2.0 * 3.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 6.0);
}

}  // namespace
