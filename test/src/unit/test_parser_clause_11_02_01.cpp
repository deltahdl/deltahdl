#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ConstantExpressionParsing, ConstantExprPrimary) {
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

TEST(ConstantExpressionParsing, ConstExprInParamDecl) {
  auto r = Parse(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  parameter DEPTH = 2 ** WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstantExpressionParsing, ConstantExprUnary) {
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

TEST(ConstantExpressionParsing, ConstantExprBinary) {
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

TEST(ConstantExpressionParsing, ConstantExprTernary) {
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

TEST(ConstantExpressionParsing, ConstantPrimaryParameterIdentifier) {
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

TEST(ConstantExpressionParsing, ConstantSelectParameterExpr) {
  auto r = Parse(
      "module m;\n"
      "  parameter int A [4] = '{1, 2, 3, 4};\n"
      "  parameter int B = A[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstExpr, IntLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("42", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, RealLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("3.14", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, StringLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("\"hello\"", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, ParameterIdentifierIsConstant) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 8}};
  auto* e = ParseExprFrom("WIDTH", f);
  EXPECT_TRUE(IsConstantExpr(e, scope));
}

TEST(ConstExpr, UnresolvedIdentifierNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("x", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, UnaryOnConstantIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("-42", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, BinaryOnConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("3 + 4", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, BinaryWithNonConstantNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("x + 4", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, TernaryOnConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? 10 : 20", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, ConcatenationOfConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{4'd1, 4'd2}", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, ReplicationOfConstantsIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{4{1'b1}}", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, Clog2ConstantSysFuncIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2(8)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, Clog2NonConstantArgNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstEvalReal, NonConstantReturnsNullopt) {
  EvalFixture f;
  auto* e = ParseExprFrom("x", f);
  auto val = ConstEvalReal(e);
  EXPECT_FALSE(val.has_value());
}

TEST(ConstExpr, UnbasedUnsizedLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("'1", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, BitsIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$bits(32'd0)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, CountonesConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$countones(8'hFF)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, OnehotConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$onehot(8'h04)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, Onehot0ConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$onehot0(8'h00)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, TimeLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("10ns", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, CastOfConstantIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("int'(3)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, CastOfNonConstantNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("int'(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, SignedIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$signed(42)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, UnsignedIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$unsigned(42)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, ConversionSysFuncNonConstantArgNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$signed(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, SqrtIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$sqrt(4.0)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, LnIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$ln(1.0)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, FloorIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$floor(3.7)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, CeilIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$ceil(3.2)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, MathSysFuncNonConstantArgNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$sqrt(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, CountbitsIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$countbits(8'hFF, 1'b1)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, IsunboundedIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$isunbounded(8)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, NonConstantSysFuncNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$time", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, NestedConstantSysFuncIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2($bits(32'd0))", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ConstExpr, TernaryWithNonConstantCondNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("x ? 10 : 20", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, ConcatenationWithNonConstantNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{4'd1, x}", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, ReplicationWithNonConstantCountNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("{x{1'b1}}", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

TEST(ConstExpr, NullExprNotConstant) {
  EXPECT_FALSE(IsConstantExpr(nullptr));
}

TEST(ConstEval, NullExprReturnsNullopt) {
  EXPECT_EQ(ConstEvalInt(nullptr), std::nullopt);
  EXPECT_EQ(ConstEvalReal(nullptr), std::nullopt);
}

}  // namespace
