#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(IntLiterals, UnsizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntLiterals, SizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 16'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntLiterals, NegativeUnsizedIsTwosComplement) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(*val, -4);
}

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
