#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(OperatorParsing, UnaryReductionAnd) {
  VerifyInitialRhsOp("module m; initial x = &a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kAmp);
}

TEST(OperatorParsing, ReductionNandAsUnaryOperator) {
  VerifyInitialRhsOp("module m; initial x = ~&a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTildeAmp);
}

TEST(OperatorParsing, UnaryReductionOr) {
  VerifyInitialRhsOp("module m; initial x = |a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kPipe);
}

TEST(OperatorParsing, ReductionNorAsUnaryOperator) {
  VerifyInitialRhsOp("module m; initial x = ~|a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTildePipe);
}

TEST(OperatorParsing, UnaryReductionXor) {
  VerifyInitialRhsOp("module m; initial x = ^a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kCaret);
}

TEST(OperatorParsing, UnaryReductionXnorTildeCaret) {
  VerifyInitialRhsOp("module m; initial x = ~^a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTildeCaret);
}

TEST(OperatorParsing, UnaryReductionXnorCaretTilde) {
  VerifyInitialRhsOp("module m; initial x = ^~a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kCaretTilde);
}

TEST(OperatorParsing, LogicalNotAsUnaryOperator) {
  VerifyInitialRhsOp("module m; initial x = !a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kBang);
}

TEST(OperatorParsing, BitwiseNotAsUnaryOperator) {
  VerifyInitialRhsOp("module m; initial x = ~a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTilde);
}

TEST(OperatorParsing, UnaryPositive) {
  VerifyInitialRhsOp("module m; initial x = +a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kPlus);
}

TEST(OperatorParsing, UnaryNegative) {
  VerifyInitialRhsOp("module m; initial x = -a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kMinus);
}

TEST(OperatorParsing, BinaryCaseEquality) {
  VerifyInitialRhsOp("module m; initial x = a === b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kEqEqEq);
}

TEST(OperatorParsing, BinaryCaseInequality) {
  VerifyInitialRhsOp("module m; initial x = a !== b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kBangEqEq);
}

TEST(OperatorParsing, BinaryWildcardEquality) {
  VerifyInitialRhsOp("module m; initial x = a ==? b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kEqEqQuestion);
}

TEST(OperatorParsing, BinaryWildcardInequality) {
  VerifyInitialRhsOp("module m; initial x = a !=? b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kBangEqQuestion);
}

TEST(OperatorParsing, BinaryPower) {
  VerifyInitialRhsOp("module m; initial x = a ** b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPower);
}

TEST(OperatorParsing, ArithShiftLeftAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a <<< b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLtLtLt);
}

TEST(OperatorParsing, ArithShiftRightAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a >>> b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kGtGtGt);
}

TEST(OperatorParsing, BinaryLogicShiftLeft) {
  VerifyInitialRhsOp("module m; initial x = a << b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLtLt);
}

TEST(OperatorParsing, BinaryLogicShiftRight) {
  VerifyInitialRhsOp("module m; initial x = a >> b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kGtGt);
}

TEST(OperatorParsing, ImplicationInSpecifyPathCondition) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (a -> b) (a => z) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, EquivalenceInSpecifyPathCondition) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (a <-> b) (a => z) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryAdd) {
  VerifyInitialRhsOp("module m; initial x = a + b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPlus);
}

TEST(OperatorParsing, BinarySubtract) {
  VerifyInitialRhsOp("module m; initial x = a - b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kMinus);
}

TEST(OperatorParsing, BinaryMultiply) {
  VerifyInitialRhsOp("module m; initial x = a * b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kStar);
}

TEST(OperatorParsing, BinaryDivide) {
  VerifyInitialRhsOp("module m; initial x = a / b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kSlash);
}

TEST(OperatorParsing, BinaryModulo) {
  VerifyInitialRhsOp("module m; initial x = a % b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPercent);
}

TEST(OperatorParsing, BinaryLogicalEquality) {
  VerifyInitialRhsOp("module m; initial x = a == b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kEqEq);
}

TEST(OperatorParsing, BinaryLogicalInequality) {
  VerifyInitialRhsOp("module m; initial x = a != b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kBangEq);
}

TEST(OperatorParsing, LogicalAndAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a && b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kAmpAmp);
}

TEST(OperatorParsing, LogicalOrAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a || b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPipePipe);
}

TEST(OperatorParsing, LessThanAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a < b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLt);
}

TEST(OperatorParsing, GreaterThanAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a > b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kGt);
}

TEST(OperatorParsing, BinaryLessEqual) {
  VerifyInitialRhsOp("module m; initial x = a <= b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLtEq);
}

TEST(OperatorParsing, BinaryGreaterEqual) {
  VerifyInitialRhsOp("module m; initial x = a >= b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kGtEq);
}

TEST(OperatorParsing, BitwiseAndAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a & b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kAmp);
}

TEST(OperatorParsing, BitwiseOrAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a | b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPipe);
}

TEST(OperatorParsing, BitwiseXorAsBinaryOperator) {
  VerifyInitialRhsOp("module m; initial x = a ^ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kCaret);
}

TEST(OperatorParsing, BinaryBitwiseXnorCaretTilde) {
  VerifyInitialRhsOp("module m; initial x = a ^~ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kCaretTilde);
}

TEST(OperatorParsing, BinaryBitwiseXnorTildeCaret) {
  VerifyInitialRhsOp("module m; initial x = a ~^ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kTildeCaret);
}

TEST(OperatorParsing, PrefixIncrement) {
  VerifyInitialExprOp("module m; initial ++x; endmodule\n", ExprKind::kUnary,
                      TokenKind::kPlusPlus);
}

TEST(OperatorParsing, PrefixDecrement) {
  VerifyInitialExprOp("module m; initial --x; endmodule\n", ExprKind::kUnary,
                      TokenKind::kMinusMinus);
}

TEST(OperatorParsing, PostfixIncrement) {
  VerifyInitialExprOp("module m; initial x++; endmodule\n",
                      ExprKind::kPostfixUnary, TokenKind::kPlusPlus);
}

TEST(OperatorParsing, PostfixDecrement) {
  VerifyInitialExprOp("module m; initial x--; endmodule\n",
                      ExprKind::kPostfixUnary, TokenKind::kMinusMinus);
}

TEST(OperatorParsing, BinaryStarRejectedAsPrefix) {
  auto r = Parse("module m; initial x = * a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinarySlashRejectedAsPrefix) {
  auto r = Parse("module m; initial x = / a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryPercentRejectedAsPrefix) {
  auto r = Parse("module m; initial x = % a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryPowerRejectedAsPrefix) {
  auto r = Parse("module m; initial x = ** a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryLessThanRejectedAsPrefix) {
  auto r = Parse("module m; initial x = < a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryEqEqRejectedAsPrefix) {
  auto r = Parse("module m; initial x = == a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryAmpAmpRejectedAsPrefix) {
  auto r = Parse("module m; initial x = && a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryPipePipeRejectedAsPrefix) {
  auto r = Parse("module m; initial x = || a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryShiftLeftRejectedAsPrefix) {
  auto r = Parse("module m; initial x = << a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryArithShiftLeftRejectedAsPrefix) {
  auto r = Parse("module m; initial x = <<< a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryArrowRejectedAsPrefix) {
  auto r = Parse("module m; initial x = -> a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryEquivalenceRejectedAsPrefix) {
  auto r = Parse("module m; initial x = <-> a; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryPlusMissingRhs) {
  auto r = Parse("module m; initial x = a + ; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryStarMissingRhs) {
  auto r = Parse("module m; initial x = a * ; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

TEST(OperatorParsing, BinaryPowerMissingRhs) {
  auto r = Parse("module m; initial x = a ** ; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 1, "11.2"));
}

static ParseResult ParseModulePathCond(const std::string& cond) {
  return Parse(
      "module m;\n"
      "  specify\n"
      "    if (" +
      cond +
      ") (a => z) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
}

TEST(OperatorParsing, UnaryModulePathLogicalNot) {
  auto r = ParseModulePathCond("!a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BitwiseNotAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("~a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ReductionAndAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("&a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ReductionNandAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("~&a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ReductionOrAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("|a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ReductionNorAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("~|a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, ReductionXorAsUnaryModulePathOperator) {
  auto r = ParseModulePathCond("^a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionXnorCaretTilde) {
  auto r = ParseModulePathCond("^~a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionXnorTildeCaret) {
  auto r = ParseModulePathCond("~^a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathLogicalEquality) {
  auto r = ParseModulePathCond("a == b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathLogicalInequality) {
  auto r = ParseModulePathCond("a != b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, LogicalAndAsBinaryModulePathOperator) {
  auto r = ParseModulePathCond("a && b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, LogicalOrAsBinaryModulePathOperator) {
  auto r = ParseModulePathCond("a || b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BitwiseAndAsBinaryModulePathOperator) {
  auto r = ParseModulePathCond("a & b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BitwiseOrAsBinaryModulePathOperator) {
  auto r = ParseModulePathCond("a | b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseXor) {
  auto r = ParseModulePathCond("a ^ b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseXnorCaretTilde) {
  auto r = ParseModulePathCond("a ^~ b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseXnorTildeCaret) {
  auto r = ParseModulePathCond("a ~^ b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
