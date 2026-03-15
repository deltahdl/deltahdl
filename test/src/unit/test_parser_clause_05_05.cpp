#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, TwoCharOperators) {
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

TEST(LexicalConventionParsing, TwoCharOperatorTokenKinds) {
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

TEST(LexicalConventionParsing, ThreeCharOperators) {
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

TEST(LexicalConventionParsing, UnaryOperatorsLeftOfOperand) {
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

TEST(LexicalConventionParsing, UnaryPrefixIncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    ++x;\n"
              "    --x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BinaryOperatorBetweenOperands) {
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

TEST(LexicalConventionParsing, AllBinaryArithmeticOperators) {
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

TEST(LexicalConventionParsing, AllBinaryBitwiseOperators) {
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

TEST(LexicalConventionParsing, ShiftOperators) {
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

TEST(LexicalConventionParsing, ConditionalOperatorThreeOperands) {
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

TEST(LexicalConventionParsing, NestedConditionalOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial x = a ? b ? c : d : e;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, CompoundAssignmentOperators) {
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

TEST(LexicalConventionParsing, SingleCharOperatorsInExpressions) {
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

TEST(LexicalConventionParsing, PostfixIncrementDecrement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x++;\n"
              "    x--;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ChainedUnaryOperators) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    x = ~~a;\n"
              "    x = !!a;\n"
              "    x = -~a;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, OperatorInContinuousAssign) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b & c;\n"
              "  assign c = ~b;\n"
              "endmodule\n"));
}

}  // namespace
