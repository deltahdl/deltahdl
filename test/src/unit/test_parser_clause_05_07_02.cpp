#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- §5.7.2: fixed-point notation ---

TEST(ParserClause05, Cl5_7_2_DecimalNotation) {
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

TEST(ParserClause05, Cl5_7_2_ZeroPointSomething) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 0.123;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_7_2_FixedPointValue) {
  auto r = Parse("module m; real x; initial x = 2.718; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserClause05, Cl5_7_2_PointFive) {
  auto r = Parse("module m; real x; initial x = 0.5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// --- §5.7.2: scientific notation ---

TEST(ParserClause05, Cl5_7_2_ScientificNotation) {
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

TEST(ParserClause05, Cl5_7_2_ExponentOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  initial r = 39e8;\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_7_2_ExponentPositiveSign) {
  auto r = Parse("module m; real x; initial x = 1.0e+2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserClause05, Cl5_7_2_ExponentNegativeSign) {
  auto r = Parse("module m; real x; initial x = 1.0e-2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserClause05, Cl5_7_2_ScientificFull) {
  auto r = Parse("module m; real x; initial x = 1.5e+3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// --- §5.7.2: exp case insensitive (e or E) ---

TEST(ParserClause05, Cl5_7_2_ExpLowercase) {
  auto r = Parse("module m; real x; initial x = 2.5e2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserClause05, Cl5_7_2_ExpUppercase) {
  auto r = Parse("module m; real x; initial x = 2.5E2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// --- §5.7.2: underscores in real numbers ---

TEST(ParserClause05, Cl5_7_2_UnderscoresInValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1_000.000_1;\n"
              "endmodule\n"));
}

// --- §5.7.2: real literal with exponent and decimal ---

TEST(ParserClause05, Cl5_7_2_WithExponent) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1.0e3 + 2.5e-1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- §5.7.2: constant primary context ---

TEST(ParserClause05, Cl5_7_2_ConstantPrimaryReal) {
  auto r = Parse("module m; parameter real R = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kRealLiteral);
}

// --- §5.7.2: real literal as initial value ---

TEST(ParserClause05, Cl5_7_2_RealDeclarationInit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.5;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_7_2_RealNegativeExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.0e-3;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_7_2_RealPositiveExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 2.5E+4;\n"
              "endmodule\n"));
}

// §11.2.1: ConstEvalReal — real literal evaluates to double.
TEST(ConstEvalReal, RealLiteralEval) {
  EvalFixture f;
  auto* e = ParseExprFrom("3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(*val, 3.14, 1e-6);
}

TEST(ParserSection11, RealLiteralAddition) {
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

}  // namespace
