#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, RealLiteralWithExponent) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 1.0e3 + 2.5e-1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh50702, RealLiteral_DecimalNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 14.72;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 14.72);
}

TEST(ParserCh50702, RealLiteral_ScientificNotation) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1.30e-2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 0.013);
}

TEST(ParserCh50702, RealLiteral_ExponentOnly) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r;\n"
              "  initial r = 39e8;\n"
              "endmodule"));
}

TEST(ParserA84, ConstantPrimaryRealLiteral) {
  auto r = Parse("module m; parameter real R = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kRealLiteral);
}

TEST(ParserA84, PrimaryRealLiteral) {
  auto r = Parse("module m; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, NumberReal) {
  auto r = Parse("module m; real x; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, SignPlus) {
  auto r = Parse("module m; real x; initial x = 1.0e+2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, SignMinus) {
  auto r = Parse("module m; real x; initial x = 1.0e-2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, RealFixedPoint) {
  auto r = Parse("module m; real x; initial x = 2.718; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, RealScientific) {
  auto r = Parse("module m; real x; initial x = 1e3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, RealScientificFull) {
  auto r = Parse("module m; real x; initial x = 1.5e+3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, FixedPointNumber) {
  auto r = Parse("module m; real x; initial x = 0.5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, ExpLowercase) {
  auto r = Parse("module m; real x; initial x = 2.5e2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserA87, ExpUppercase) {
  auto r = Parse("module m; real x; initial x = 2.5E2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}
TEST(ParserSection11, Sec11_1_RealLiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 3.14;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

TEST(ParserSection6, RealLiteralDecimalPoint) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.5;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralScientificNotation) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.3e2;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralNegativeExponent) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.0e-3;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralPositiveExponent) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 2.5E+4;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralUnderscoresInValue) {

  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1_000.000_1;\n"
              "endmodule\n"));
}

TEST(ParserSection6, RealLiteralZeroPointSomething) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 0.123;\n"
              "endmodule\n"));
}

}
