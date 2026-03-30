

#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(OperatorParsing, BinaryDiv) {
  auto r = Parse("module m; initial x = a / b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
}

TEST(OperatorParsing, BinaryMod) {
  auto r = Parse("module m; initial x = a % b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
}

TEST(OperatorAndExpressionParsing, ComplexMixedExpressionParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = (a + b) * c - d / e % f;\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, ArithmeticMul) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a * b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(OperatorParsing, UnaryPlus) {
  auto r = Parse("module m; initial x = +a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(OperatorParsing, UnaryMinus) {
  auto r = Parse("module m; initial x = -a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(OperatorParsing, BinaryAdd) {
  auto r = Parse("module m; initial x = a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(OperatorParsing, BinarySub) {
  auto r = Parse("module m; initial x = a - b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kMinus);
}

TEST(OperatorAndExpressionParsing, BinaryPowerOperator) {
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

TEST(AssignmentParsing, ExprAddition) {
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

TEST(OperatorAndExpressionParsing, RealMultiplication) {
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

TEST(OperatorParsing, UnaryMinusPrecedenceOverAdd) {
  auto r = Parse("module m; initial x = -a + b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kMinus);
}

TEST(OperatorParsing, UnaryMinusPrecedenceOverMul) {
  auto r = Parse("module m; initial x = -a * b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kMinus);
}

TEST(ConstExpr, PowerOperatorInConstantExpr) {
  EvalFixture f;
  ScopeMap scope;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f), scope), 1024);
}

}  // namespace
