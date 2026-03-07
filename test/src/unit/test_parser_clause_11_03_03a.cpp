#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §11.3.3: Unsized unbased integer literal as expression.
TEST(IntLiterals, UnsizedUnbasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 12u);
}

// §11.3.3: Unsized based integer literal.
TEST(IntLiterals, UnsizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// §11.3.3: Sized based integer literal.
TEST(IntLiterals, SizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 16'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

// §11.3.3: Negative unsized literal is two's-complement.
// -12 is parsed as unary minus on 12.
TEST(IntLiterals, NegativeUnsizedIsTwosComplement) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(*val, -4);
}

// §11.3.3: Hex literal.
TEST(IntLiterals, HexLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xFFu);
}

// §11.3.3: Binary literal.
TEST(IntLiterals, BinaryLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 4'b1010;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 0xAu);
}

// §11.3.3: Octal literal.
TEST(IntLiterals, OctalLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 8'o77;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 077u);
}

}  // namespace
