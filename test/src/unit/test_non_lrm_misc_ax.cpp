// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// § binary_operator ::= >=
TEST(ParserA86, BinaryGreaterOrEqual) {
  auto r = Parse("module m; initial x = (a >= b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtEq);
}

// =============================================================================
// A.8.6 Operators — binary_operator (bitwise)
// =============================================================================
// § binary_operator ::= &
TEST(ParserA86, BinaryBitwiseAnd) {
  auto r = Parse("module m; initial x = a & b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

// § binary_operator ::= |
TEST(ParserA86, BinaryBitwiseOr) {
  auto r = Parse("module m; initial x = a | b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
}

// § binary_operator ::= ^
TEST(ParserA86, BinaryBitwiseXor) {
  auto r = Parse("module m; initial x = a ^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
}

// § binary_operator ::= ^~
TEST(ParserA86, BinaryBitwiseXnor) {
  auto r = Parse("module m; initial x = a ^~ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kCaretTilde);
}

// § binary_operator ::= ~^
TEST(ParserA86, BinaryBitwiseXnorAlt) {
  auto r = Parse("module m; initial x = a ~^ b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kTildeCaret);
}

// =============================================================================
// A.8.6 Operators — binary_operator (shift)
// =============================================================================
// § binary_operator ::= >>
TEST(ParserA86, BinaryLogicalRightShift) {
  auto r = Parse("module m; initial x = a >> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// § binary_operator ::= <<
TEST(ParserA86, BinaryLogicalLeftShift) {
  auto r = Parse("module m; initial x = a << 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

// § binary_operator ::= >>>
TEST(ParserA86, BinaryArithRightShift) {
  auto r = Parse("module m; initial x = a >>> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// § binary_operator ::= <<<
TEST(ParserA86, BinaryArithLeftShift) {
  auto r = Parse("module m; initial x = a <<< 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

// =============================================================================
// A.8.6 Operators — binary_operator (implication)
// =============================================================================
// § binary_operator ::= ->
TEST(ParserA86, BinaryImplication) {
  auto r = Parse("module m; initial x = (a -> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

// § binary_operator ::= <->
TEST(ParserA86, BinaryEquivalence) {
  auto r = Parse("module m; initial x = (a <-> b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
}

// =============================================================================
// A.8.6 Operators — inc_or_dec_operator
// =============================================================================
// § inc_or_dec_operator ::= ++ (prefix)
TEST(ParserA86, IncOrDecPrefixIncrement) {
  auto r = Parse("module m; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

// § inc_or_dec_operator ::= -- (prefix)
TEST(ParserA86, IncOrDecPrefixDecrement) {
  auto r = Parse("module m; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// § inc_or_dec_operator ::= ++ (postfix)
TEST(ParserA86, IncOrDecPostfixIncrement) {
  auto r = Parse("module m; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

// § inc_or_dec_operator ::= -- (postfix)
TEST(ParserA86, IncOrDecPostfixDecrement) {
  auto r = Parse("module m; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

// =============================================================================
// A.8.6 Operators — unary_module_path_operator
// =============================================================================
// § unary_module_path_operator — ! in specify path condition
TEST(ParserA86, UnaryModulePathNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § unary_module_path_operator — ~ in specify path condition
TEST(ParserA86, UnaryModulePathBitwiseNot) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.6 Operators — binary_module_path_operator
// =============================================================================
// § binary_module_path_operator — == in specify path condition
TEST(ParserA86, BinaryModulePathEq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — != in specify path condition
TEST(ParserA86, BinaryModulePathNeq) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — && in specify path condition
TEST(ParserA86, BinaryModulePathLogicalAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a && b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — || in specify path condition
TEST(ParserA86, BinaryModulePathLogicalOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — & in specify path condition
TEST(ParserA86, BinaryModulePathBitwiseAnd) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a & b) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — | in specify path condition
TEST(ParserA86, BinaryModulePathBitwiseOr) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a | b) (a => y) = 6;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ^ in specify path condition
TEST(ParserA86, BinaryModulePathXor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^ b) (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ^~ in specify path condition
TEST(ParserA86, BinaryModulePathXnor) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § binary_module_path_operator — ~^ in specify path condition
TEST(ParserA86, BinaryModulePathXnorAlt) {
  auto r = Parse(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ~^ b) (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.7 Numbers — Parser
// =============================================================================
// § number — integral_number
TEST(ParserA87, NumberIntegral) {
  auto r = Parse("module m; logic [7:0] x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § number — real_number
TEST(ParserA87, NumberReal) {
  auto r = Parse("module m; real x; initial x = 3.14; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § integral_number — decimal_number (unsized)
TEST(ParserA87, IntegralDecimal) {
  auto r = Parse("module m; int x; initial x = 255; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 255u);
}

// § integral_number — octal_number
TEST(ParserA87, IntegralOctal) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § integral_number — binary_number
TEST(ParserA87, IntegralBinary) {
  auto r =
      Parse("module m; logic [7:0] x; initial x = 8'b10101010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xAAu);
}

// § integral_number — hex_number
TEST(ParserA87, IntegralHex) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

// § decimal_number — unsigned_number
TEST(ParserA87, DecimalUnsigned) {
  auto r = Parse("module m; int x; initial x = 0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0u);
}

// § decimal_number — [size] decimal_base unsigned_number
TEST(ParserA87, DecimalSizedBase) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'd200; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 200u);
}

// § decimal_number — [size] decimal_base x_digit
TEST(ParserA87, DecimalXDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § decimal_number — [size] decimal_base z_digit
TEST(ParserA87, DecimalZDigit) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'dz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// § binary_number — [size] binary_base binary_value
TEST(ParserA87, BinaryNumber) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b1100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xCu);
}

// § octal_number — [size] octal_base octal_value
TEST(ParserA87, OctalNumber) {
  auto r = Parse("module m; logic [11:0] x; initial x = 12'o7654; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 07654u);
}

// § hex_number — [size] hex_base hex_value
TEST(ParserA87, HexNumber) {
  auto r = Parse("module m; logic [15:0] x; initial x = 16'hABCD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xABCDu);
}

// § sign — + (in real exponent)
TEST(ParserA87, SignPlus) {
  auto r = Parse("module m; real x; initial x = 1.0e+2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § sign — - (in real exponent)
TEST(ParserA87, SignMinus) {
  auto r = Parse("module m; real x; initial x = 1.0e-2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § size — unsigned_number (various widths)
TEST(ParserA87, Size1Bit) {
  auto r = Parse("module m; logic x; initial x = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 1u);
}

TEST(ParserA87, Size32Bit) {
  auto r = Parse("module m; int x; initial x = 32'd100; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 100u);
}

// § real_number — fixed_point_number
TEST(ParserA87, RealFixedPoint) {
  auto r = Parse("module m; real x; initial x = 2.718; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § real_number — unsigned_number exp unsigned_number
TEST(ParserA87, RealScientific) {
  auto r = Parse("module m; real x; initial x = 1e3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § real_number — unsigned_number . unsigned_number exp sign unsigned_number
TEST(ParserA87, RealScientificFull) {
  auto r = Parse("module m; real x; initial x = 1.5e+3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § fixed_point_number — unsigned_number . unsigned_number
TEST(ParserA87, FixedPointNumber) {
  auto r = Parse("module m; real x; initial x = 0.5; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § exp — e
TEST(ParserA87, ExpLowercase) {
  auto r = Parse("module m; real x; initial x = 2.5e2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § exp — E
TEST(ParserA87, ExpUppercase) {
  auto r = Parse("module m; real x; initial x = 2.5E2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kRealLiteral);
}

// § unsigned_number — decimal_digit { _ | decimal_digit }
TEST(ParserA87, UnsignedNumberWithUnderscores) {
  auto r = Parse("module m; int x; initial x = 1_000_000; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 1000000u);
}

// § binary_value — binary_digit { _ | binary_digit }
TEST(ParserA87, BinaryValueWithUnderscores) {
  auto r =
      Parse("module m; logic [7:0] x; initial x = 8'b1010_1010; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xAAu);
}

// § octal_value — octal_digit { _ | octal_digit }
TEST(ParserA87, OctalValueWithUnderscores) {
  auto r =
      Parse("module m; logic [11:0] x; initial x = 12'o77_77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 07777u);
}

// § hex_value — hex_digit { _ | hex_digit }
TEST(ParserA87, HexValueWithUnderscores) {
  auto r =
      Parse("module m; logic [15:0] x; initial x = 16'hAB_CD; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xABCDu);
}

// § decimal_base — 'd
TEST(ParserA87, DecimalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

// § decimal_base — 'D
TEST(ParserA87, DecimalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'D99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

// § decimal_base — 'sd (signed)
TEST(ParserA87, DecimalBaseSignedLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'sd99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

// § decimal_base — 'SD
TEST(ParserA87, DecimalBaseSignedUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SD99; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 99u);
}

// § binary_base — 'b
TEST(ParserA87, BinaryBaseLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § binary_base — 'B
TEST(ParserA87, BinaryBaseUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'B1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § binary_base — 'sb (signed)
TEST(ParserA87, BinaryBaseSignedLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'sb1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § binary_base — 'SB
TEST(ParserA87, BinaryBaseSignedUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'SB1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § octal_base — 'o
TEST(ParserA87, OctalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'O
TEST(ParserA87, OctalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'O77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'so (signed)
TEST(ParserA87, OctalBaseSignedLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'so77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'SO
TEST(ParserA87, OctalBaseSignedUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SO77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § hex_base — 'h
TEST(ParserA87, HexBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'H
TEST(ParserA87, HexBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'HAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'sh (signed)
TEST(ParserA87, HexBaseSignedLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'shAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'SH
TEST(ParserA87, HexBaseSignedUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SHAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § decimal_digit — 0 through 9
TEST(ParserA87, DecimalDigitAll) {
  auto r = Parse("module m; int x; initial x = 1234567890; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1234567890u);
}

// § binary_digit — 0 and 1
TEST(ParserA87, BinaryDigitZeroOne) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b0101; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 5u);
}

}  // namespace
