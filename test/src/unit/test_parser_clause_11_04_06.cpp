#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OperatorParsing, BinaryWildcardEq) {
  auto r = Parse("module m; initial x = (a ==? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqQuestion);
}

TEST(OperatorParsing, BinaryWildcardNeq) {
  auto r = Parse("module m; initial x = (a !=? b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kBangEqQuestion);
}

TEST(Precedence, WildcardEqualitySamePrecedenceAsLogicalEquality) {
  auto r = Parse("module m; initial x = a ==? b != c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kEqEqQuestion);
}

TEST(OperatorAndExpressionParsing, WildcardEqInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (data ==? 8'b1xx0_xx10)\n"
      "      $display(\"match\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
