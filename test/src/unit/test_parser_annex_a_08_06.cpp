#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OperatorParsing, UnaryReductionAnd) {
  VerifyInitialRhsOp("module m; initial x = &a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kAmp);
}

TEST(OperatorParsing, UnaryReductionNand) {
  VerifyInitialRhsOp("module m; initial x = ~&a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTildeAmp);
}

TEST(OperatorParsing, UnaryReductionOr) {
  VerifyInitialRhsOp("module m; initial x = |a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kPipe);
}

TEST(OperatorParsing, UnaryReductionNor) {
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

TEST(OperatorParsing, UnaryLogicalNot) {
  VerifyInitialRhsOp("module m; initial x = !a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kBang);
}

TEST(OperatorParsing, UnaryBitwiseNot) {
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

TEST(OperatorParsing, BinaryArithShiftLeft) {
  VerifyInitialRhsOp("module m; initial x = a <<< b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLtLtLt);
}

TEST(OperatorParsing, BinaryArithShiftRight) {
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

TEST(OperatorParsing, BinaryImplication) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (a -> b) (a => z) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryEquivalence) {
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

TEST(OperatorParsing, BinaryLogicalAnd) {
  VerifyInitialRhsOp("module m; initial x = a && b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kAmpAmp);
}

TEST(OperatorParsing, BinaryLogicalOr) {
  VerifyInitialRhsOp("module m; initial x = a || b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPipePipe);
}

TEST(OperatorParsing, BinaryLessThan) {
  VerifyInitialRhsOp("module m; initial x = a < b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kLt);
}

TEST(OperatorParsing, BinaryGreaterThan) {
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

TEST(OperatorParsing, BinaryBitwiseAnd) {
  VerifyInitialRhsOp("module m; initial x = a & b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kAmp);
}

TEST(OperatorParsing, BinaryBitwiseOr) {
  VerifyInitialRhsOp("module m; initial x = a | b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPipe);
}

TEST(OperatorParsing, BinaryBitwiseXor) {
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
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinarySlashRejectedAsPrefix) {
  auto r = Parse("module m; initial x = / a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryPercentRejectedAsPrefix) {
  auto r = Parse("module m; initial x = % a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryPowerRejectedAsPrefix) {
  auto r = Parse("module m; initial x = ** a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryLessThanRejectedAsPrefix) {
  auto r = Parse("module m; initial x = < a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryEqEqRejectedAsPrefix) {
  auto r = Parse("module m; initial x = == a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryAmpAmpRejectedAsPrefix) {
  auto r = Parse("module m; initial x = && a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryPipePipeRejectedAsPrefix) {
  auto r = Parse("module m; initial x = || a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryShiftLeftRejectedAsPrefix) {
  auto r = Parse("module m; initial x = << a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryArithShiftLeftRejectedAsPrefix) {
  auto r = Parse("module m; initial x = <<< a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryArrowRejectedAsPrefix) {
  auto r = Parse("module m; initial x = -> a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryEquivalenceRejectedAsPrefix) {
  auto r = Parse("module m; initial x = <-> a; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryPlusMissingRhs) {
  auto r = Parse("module m; initial x = a + ; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryStarMissingRhs) {
  auto r = Parse("module m; initial x = a * ; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(OperatorParsing, BinaryPowerMissingRhs) {
  auto r = Parse("module m; initial x = a ** ; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// -- Module-path operators (unary_module_path_operator /
//    binary_module_path_operator). Their natural syntactic home is a module
//    path condition, so exercise them through a specify state-dependent path.

// Parse a specify block whose state-dependent path condition holds the given
// module-path expression, expecting a clean parse.
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

TEST(OperatorParsing, UnaryModulePathBitwiseNot) {
  auto r = ParseModulePathCond("~a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionAnd) {
  auto r = ParseModulePathCond("&a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionNand) {
  auto r = ParseModulePathCond("~&a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionOr) {
  auto r = ParseModulePathCond("|a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionNor) {
  auto r = ParseModulePathCond("~|a");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, UnaryModulePathReductionXor) {
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

TEST(OperatorParsing, BinaryModulePathLogicalAnd) {
  auto r = ParseModulePathCond("a && b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathLogicalOr) {
  auto r = ParseModulePathCond("a || b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseAnd) {
  auto r = ParseModulePathCond("a & b");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorParsing, BinaryModulePathBitwiseOr) {
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
