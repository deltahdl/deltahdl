#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, DecimalNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 14.72;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 14.72);
}

TEST(LexicalConventionParsing, LeadingZeroDecimal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 0.123;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, FixedPointValue) {
  auto r = Parse("module m; real x; initial x = 2.718; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, PointFive) {
  auto r = Parse("module m; real x; initial x = 0.5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, ScientificNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1.30e-2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 0.013);
}

TEST(LexicalConventionParsing, ExponentOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  initial r = 39e8;\n"
              "endmodule"));
}

TEST(LexicalConventionParsing, ExponentPositiveSign) {
  auto r = Parse("module m; real x; initial x = 1.0e+2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, ExponentNegativeSign) {
  auto r = Parse("module m; real x; initial x = 1.0e-2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, ScientificWithPositiveSign) {
  auto r = Parse("module m; real x; initial x = 1.5e+3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, ExpLowercase) {
  auto r = Parse("module m; real x; initial x = 2.5e2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, ExpUppercase) {
  auto r = Parse("module m; real x; initial x = 2.5E2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, UnderscoresInValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1_000.000_1;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ExponentInAddition) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1.0e3 + 2.5e-1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, ConstantPrimaryReal) {
  auto r = Parse("module m; parameter real R = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, RealDeclarationInit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.5;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, RealNegativeExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.0e-3;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, RealPositiveExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 2.5E+4;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, UnderscoreStrippedInValue) {
  auto r = Parse("module m; real x; initial x = 1_000.000_1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 1000.0001);
}

TEST(LexicalConventionParsing, ExponentOnlyValue) {
  auto r = Parse("module m; real x; initial x = 39e8; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 39e8);
}

TEST(ConstEvalReal, RealLiteralEval) {
  EvalFixture f;
  auto* e = ParseExprFrom("3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(val.value_or(0.0), 3.14, 1e-6);
}

TEST(ConstEvalReal, ScientificNotation) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.5e3", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 1500.0);
}

TEST(ConstEvalReal, ExponentOnly) {
  EvalFixture f;
  auto* e = ParseExprFrom("39e8", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 39e8);
}

TEST(OperatorAndExpressionParsing, RealLiteralAddition) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1.5 + 2.5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kRealLiteral);
}

TEST(LexicalConventionParsing, RealLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  real r;\n"
              "  initial r = 3.14;\n"
              "endmodule\n"));
}

}  // namespace
