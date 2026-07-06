#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ConstEval, Logical) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 && 0", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 1", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 || 0", f)), 0);
}

TEST(ConstEval, Unary) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("-5", f)), -5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!0", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("!5", f)), 0);
}

// Constant-expression operand form: logical operands that are module parameters
// are folded by the elaborator's constant evaluator to fix a localparam's
// value; reading the localparam at run time observes the folded result.
// Parameters reach the constant evaluator through a different declaration path
// than the integer literals exercised by ConstEval.Logical.
TEST(ConstEval, LogicalOverParameters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int A = 237;\n"
      "  parameter int B = 0;\n"
      "  localparam bit R_AND = A && B;\n"
      "  localparam bit R_OR = A || B;\n"
      "  logic y_and, y_or;\n"
      "  initial begin\n"
      "    y_and = R_AND;\n"
      "    y_or = R_OR;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y_and = f.ctx.FindVariable("y_and");
  auto* y_or = f.ctx.FindVariable("y_or");
  ASSERT_NE(y_and, nullptr);
  ASSERT_NE(y_or, nullptr);
  EXPECT_EQ(y_and->value.ToUint64(), 0u);
  EXPECT_EQ(y_or->value.ToUint64(), 1u);
}

// Same constant-folding rule for the unary logical negation, with a localparam
// operand — a distinct constant form from a literal.
TEST(ConstEval, LogicalNotOverLocalparam) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 5;\n"
      "  localparam bit R = !P;\n"
      "  logic y;\n"
      "  initial y = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
}

TEST(OperatorElaboration, UnaryLogicalNotElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, a;\n"
      "  initial x = !a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryImplicationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (1'b0 -> 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryEquivalenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (1'b1 <-> 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryLogicalAndElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, a, b;\n"
      "  initial x = a && b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryLogicalOrElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x, a, b;\n"
      "  initial x = a || b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
