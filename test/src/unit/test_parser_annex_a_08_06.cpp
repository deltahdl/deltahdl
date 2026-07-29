#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// A.8.6 gathers the operator tokens into four productions: unary_operator,
// binary_operator, unary_module_path_operator and binary_module_path_operator.
// Where an operator also has a clause of its own — §11.4.4 relational, §11.4.7
// logical, §11.4.8 bitwise, §11.4.9 reduction, §11.4.10 shift and §30.4.4.1
// module paths — the clause file holds the plain name and covers the prose, and
// the case here is named `<Op>As<Production>` for the production it places the
// token in.

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

// A.8.6 lists `->` under binary_operator, but the operands come from a specify
// path condition here rather than from an expression, so the name states that
// context. §11.4.7's file carries the expression form.
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

// `<->` likewise reaches the parser through a specify path condition here, so
// the name states that context; §11.4.7's file carries the expression form.
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
