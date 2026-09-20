#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(RealLiteralParsing, DecimalNotation) {
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

TEST(RealLiteralParsing, LeadingZeroDecimal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 0.123;\n"
              "endmodule\n"));
}

TEST(RealLiteralParsing, ScientificNotation) {
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

TEST(RealLiteralParsing, ConstantPrimaryReal) {
  auto r = Parse("module m; parameter real R = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kRealLiteral);
}

TEST(RealLiteralParsing, RealDeclarationInit) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.5;\n"
              "endmodule\n"));
}

TEST(RealLiteralParsing, RealNegativeExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 1.0e-3;\n"
              "endmodule\n"));
}

TEST(RealLiteralParsing, RealPositiveExponent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real r = 2.5E+4;\n"
              "endmodule\n"));
}

TEST(RealLiteralParsing, UnderscoreStrippedInValue) {
  auto r = Parse("module m; real x; initial x = 1_000.000_1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
  EXPECT_DOUBLE_EQ(rhs->real_val, 1000.0001);
}

TEST(RealLiteralParsing, ExponentOnlyValue) {
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

TEST(RealLiteralParsing, RealLiteralAddition) {
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

// §5.7.2 lists `.12`, `9.`, `4.E3` and `.2e-7` as invalid real numbers for
// lacking a digit on one side of the decimal point. The lexer reads each as the
// real literal it was written to be and reports it there, so each assignment of
// the sv-tests module is reported under the subclause whose rule it breaks, on
// its own line.
TEST(RealLiteralParsing, PointWithoutADigitOnEachSideIsReportedUnderClause572) {
  auto r = Parse(
      "module top();\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a = .12;\n"
      "    a = 9.;\n"
      "    a = 4.E3;\n"
      "    a = .2e-7;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "'.12' has no digit before", 4, "5.7.2"));
  EXPECT_TRUE(ReportedError(r.diags, "'9.' has no digit after", 5, "5.7.2"));
  EXPECT_TRUE(ReportedError(r.diags, "'4.E3' has no digit after", 6, "5.7.2"));
  EXPECT_TRUE(
      ReportedError(r.diags, "'.2e-7' has no digit before", 7, "5.7.2"));
}

// The whole spelling is one token, so the statements are parsed in step: no
// report of a member name expected after the point, which is what §23.3.2.3 had
// said of the `.` handed to it, and none of a token left over after the
// literal, which is what §12.3 had said of the digits.
TEST(RealLiteralParsing, PointWithoutADigitLeavesNoLeftoverTokenReport) {
  auto r = Parse(
      "module top();\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a = .12;\n"
      "    a = 9.;\n"
      "    a = 4.E3;\n"
      "    a = .2e-7;\n"
      "  end\n"
      "endmodule\n");
  for (const auto& d : r.diags) {
    EXPECT_EQ(d.subclause, "5.7.2") << d.message;
  }
}

}  // namespace
