#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_5_TwoCharOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a == b);\n"
              "    x = (a != b);\n"
              "    x = (a <= b);\n"
              "    x = (a >= b);\n"
              "    x = (a && b);\n"
              "    x = (a || b);\n"
              "    x = a << 1;\n"
              "    x = a >> 1;\n"
              "    a += 1;\n"
              "    a -= 1;\n"
              "    a *= 2;\n"
              "    a /= 2;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_TwoCharOperatorTokenKinds) {
  auto r = Parse(
      "module m;\n"
      "  initial x = (a == b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
}

TEST(ParserClause05, Cl5_5_ThreeCharOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = (a === b);\n"
              "    x = (a !== b);\n"
              "    x = a <<< 2;\n"
              "    x = a >>> 2;\n"
              "    x = (a ==? b);\n"
              "    x = (a !=? b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_UnaryOperatorsLeftOfOperand) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = ~a;\n"
      "    x = !a;\n"
      "    x = -a;\n"
      "    x = +a;\n"
      "    x = &a;\n"
      "    x = |a;\n"
      "    x = ^a;\n"
      "    x = ~&a;\n"
      "    x = ~|a;\n"
      "    x = ~^a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kTilde);
}

TEST(ParserClause05, Cl5_5_UnaryPrefixIncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    ++x;\n"
              "    --x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_BinaryOperatorBetweenOperands) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserClause05, Cl5_5_AllBinaryArithmeticOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a ** b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_AllBinaryBitwiseOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a ~^ b;\n"
              "    x = a ^~ b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_ShiftOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a << 1;\n"
              "    x = a >> 1;\n"
              "    x = a <<< 1;\n"
              "    x = a >>> 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_ConditionalOperatorThreeOperands) {
  auto r = Parse(
      "module m;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

TEST(ParserClause05, Cl5_5_NestedConditionalOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = a ? b ? c : d : e;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_CompoundAssignmentOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    a += 1;\n"
              "    a -= 1;\n"
              "    a *= 2;\n"
              "    a /= 2;\n"
              "    a %= 3;\n"
              "    a &= 8'hFF;\n"
              "    a |= 8'h0F;\n"
              "    a ^= 8'hAA;\n"
              "    a <<= 1;\n"
              "    a >>= 1;\n"
              "    a <<<= 1;\n"
              "    a >>>= 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_5_SingleCharOperatorsInExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = a + b;\n"
              "    x = a - b;\n"
              "    x = a * b;\n"
              "    x = a / b;\n"
              "    x = a % b;\n"
              "    x = a & b;\n"
              "    x = a | b;\n"
              "    x = a ^ b;\n"
              "    x = a < b;\n"
              "    x = a > b;\n"
              "  end\n"
              "endmodule\n"));
}

}
