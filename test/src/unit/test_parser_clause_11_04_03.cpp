#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ParserA86, BinaryDiv) {
  auto r = Parse("module m; initial x = a / b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

TEST(ParserA86, BinaryMod) {
  auto r = Parse("module m; initial x = a % b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

TEST(ParserA86, BinaryPower) {
  auto r = Parse("module m; initial x = a ** b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
}

TEST(ParserSection11, ComplexMixedExpressionParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = (a + b) * c - d / e % f;\n"
              "endmodule\n"));
}

TEST(ParserSection11, UnaryPlusOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = +a;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
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

TEST(ParserSection11, RealMultiplication) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = 3.14 * 2.0;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, ArithmeticAdd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserSection11, ArithmeticSub) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a - b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserSection11, ArithmeticMul) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a * b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, ArithmeticMod) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a % b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

TEST(ParserSection11, ArithmeticPower) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ** b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
}

TEST(ParserSection11, UnaryNegation) {
  auto r = Parse(
      "module t;\n"
      "  initial x = -a;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserA83, ExprBinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserA86, UnaryPlus) {
  auto r = Parse("module m; initial x = +a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserA86, UnaryMinus) {
  auto r = Parse("module m; initial x = -a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserA86, BinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserA86, BinarySub) {
  auto r = Parse("module m; initial x = a - b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(ParserA86, BinaryMul) {
  auto r = Parse("module m; initial x = a * b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, Sec11_1_BinaryPowerOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = base ** exp;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserSection11, ArithmeticDiv) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a / b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

TEST(ParserSection6, RealInExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a, b, c;\n"
              "  initial begin\n"
              "    a = 1.5;\n"
              "    b = 2.5;\n"
              "    c = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserCh505, Operator_BinaryAdd) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserCh505, Operator_Power) {
  EXPECT_TRUE(ParseOk("module m; initial x = 2 ** 10; endmodule"));
}

TEST(Eval, Addition) {
  ExprFixture f;
  auto* expr = ParseExprFrom("10 + 32", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(ParserSection10, Sec10_4_1_ExprAddition) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// §11.2.1: ConstEvalReal — unary minus on real.
TEST(ConstEvalReal, UnaryMinusOnReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("-3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(*val, -3.14, 1e-6);
}

// §11.2.1: ConstEvalReal — binary add on reals.
TEST(ConstEvalReal, BinaryAddReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.5 + 2.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 4.0);
}

// §11.2.1: ConstEvalReal — binary multiply on reals.
TEST(ConstEvalReal, BinaryMulReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("2.0 * 3.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 6.0);
}

}  // namespace
