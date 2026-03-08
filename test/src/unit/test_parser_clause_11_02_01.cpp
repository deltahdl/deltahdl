#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA83, ConstantExprPrimary) {
  auto r = Parse(
      "module m #(parameter int P = 42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(params[0].second->int_val, 42u);
}

TEST(ParserSection11, ConstExprInParamDecl) {
  auto r = Parse(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  parameter DEPTH = 2 ** WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA83, ConstantExprUnary) {
  auto r = Parse(
      "module m #(parameter int P = -1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kUnary);
  EXPECT_EQ(params[0].second->op, TokenKind::kMinus);
}

TEST(ParserA83, ConstantExprBinary) {
  auto r = Parse(
      "module m #(parameter int P = 3 + 4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kBinary);
  EXPECT_EQ(params[0].second->op, TokenKind::kPlus);
}

TEST(ParserA83, ConstantExprTernary) {
  auto r = Parse(
      "module m #(parameter int P = 1 ? 10 : 20);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kTernary);
}

TEST(ConstEval, ScopedIdentifier) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH", f), scope), 16);
}

TEST(ConstEval, ScopedExprWithParam) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH > 8", f), scope), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("WIDTH + 4", f), scope), 20);
}

TEST(ParserA84, ConstantPrimaryParameterIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[1];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kIdentifier);
}

TEST(ParserA84, ConstantSelectParameterExpr) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [4] = '{1, 2, 3, 4};\n"
      "  parameter int B = A[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §11.2.1: IsConstantExpr — integer literal is constant.
TEST(ConstExpr, IntLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("42", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — real literal is constant.
TEST(ConstExpr, RealLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("3.14", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — string literal is constant.
TEST(ConstExpr, StringLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("\"hello\"", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — parameter identifier is constant
// when resolved in scope.
TEST(ConstExpr, ParameterIdentifierIsConstant) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 8}};
  auto* e = ParseExprFrom("WIDTH", f);
  EXPECT_TRUE(IsConstantExpr(e, scope));
}

// §11.2.1: IsConstantExpr — unresolved identifier is not constant.
TEST(ConstExpr, UnresolvedIdentifierNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("x", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — unary on constant is constant.
TEST(ConstExpr, UnaryOnConstantIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("-42", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — binary on constants is constant.
TEST(ConstExpr, BinaryOnConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("3 + 4", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — binary with non-constant operand is not constant.
TEST(ConstExpr, BinaryWithNonConstantNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("x + 4", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — ternary on constants is constant.
TEST(ConstExpr, TernaryOnConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? 10 : 20", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — concatenation of constants is constant.
TEST(ConstExpr, ConcatenationOfConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{4'd1, 4'd2}", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: IsConstantExpr — replication of constants is constant.
TEST(ConstExpr, ReplicationOfConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{4{1'b1}}", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: Constant system function call — $clog2 with constant arg.
TEST(ConstExpr, Clog2ConstantSysFuncIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2(8)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: Constant system function call — $clog2 with non-constant arg
// is not constant.
TEST(ConstExpr, Clog2NonConstantArgNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

// §11.2.1: ConstEvalReal — non-constant returns nullopt.
TEST(ConstEvalReal, NonConstantReturnsNullopt) {
  EvalFixture f;
  auto* e = ParseExprFrom("x", f);
  auto val = ConstEvalReal(e);
  EXPECT_FALSE(val.has_value());
}

}  // namespace
