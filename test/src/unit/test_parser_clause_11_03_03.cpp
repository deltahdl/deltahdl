#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(IntegerLiteralParsing, LiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 42;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedUnbasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->int_val, 12u);
}

TEST(IntegerLiteralParsing, UnsizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, UnsizedBasedSignedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 'sd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, SizedBasedLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 16'd12;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

TEST(IntegerLiteralParsing, NegativeBeforeSizedLiteral) {
  auto r = Parse("module m; logic [7:0] x; initial x = -8'd6; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralParsing, NegativeBeforeUnsizedBasedLiteral) {
  auto r = Parse("module m; integer x; initial x = -'d12; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralParsing, NegativeBeforeUnsizedSignedBasedLiteral) {
  auto r = Parse("module m; integer x; initial x = -'sd12; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralParsing, NegativeBeforeSizedSignedBasedLiteral) {
  auto r = Parse("module m; integer x; initial x = -4'sd12; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralParsing, NegativeUnsizedIsTwosComplement) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralParsing, IntegerLiteralInExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [31:0] x;\n"
              "  initial x = 32'd42;\n"
              "endmodule\n"));
}

}  // namespace
