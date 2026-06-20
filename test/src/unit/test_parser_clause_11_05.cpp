#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, IdentifierAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = foo;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, SystemFunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$clog2");
}

TEST(OperatorAndExpressionParsing, FunctionCallExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = my_func(a, b);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "my_func");
  EXPECT_EQ(rhs->args.size(), 2u);
}

TEST(OperatorAndExpressionParsing, ParameterReferenceAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  int x;\n"
      "  initial x = P;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "P");
}

TEST(OperatorAndExpressionParsing, BitSelectAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic b;\n"
      "  initial b = a[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, PartSelectAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial b = a[3:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, UnpackedArrayElementAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  int x;\n"
      "  initial x = arr[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->text, "arr");
}

TEST(OperatorAndExpressionParsing, ConcatenationAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, NestedConcatenationAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] d;\n"
      "  initial d = {a, {b, c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
  ASSERT_NE(rhs->elements[1], nullptr);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements[1]->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, ConcatenationWithMixedOperandTypes) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial x = {a, 4'b1010, a[3:0]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements[2]->kind, ExprKind::kSelect);
}

TEST(OperatorAndExpressionParsing, SimpleOperandIdentifier) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial x = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_TRUE(IsSimpleOperand(rhs));
  EXPECT_FALSE(rhs->is_parenthesized);
}

TEST(OperatorAndExpressionParsing, SimpleOperandBitSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial x = a[3];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandPartSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial x = a[3:0];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandUnpackedArrayElement) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr[2];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandConcatenation) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial x = {a, b};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandFunctionCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = foo(1, 2);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandIntegerLiteral) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, ParenthesizedExpressionIsNotSimpleOperand) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (1'b1 + 1'b1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_TRUE(rhs->is_parenthesized);
  EXPECT_FALSE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, BinaryExpressionIsNotSimpleOperand) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 1'b1 - 2'b00;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_FALSE(rhs->is_parenthesized);
  EXPECT_FALSE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, ParenthesizedPrimaryIsNotSimpleOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial x = (a);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_TRUE(rhs->is_parenthesized);
  EXPECT_FALSE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing,
     LrmExampleSubExpressionsAreNotSimpleOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 1'b1 - 2'b00 + (1'b1 + 1'b1);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_FALSE(IsSimpleOperand(rhs->lhs));
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_TRUE(rhs->rhs->is_parenthesized);
  EXPECT_FALSE(IsSimpleOperand(rhs->rhs));
}

TEST(OperatorAndExpressionParsing, NetReferenceAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  initial x = w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "w");
}

TEST(OperatorAndExpressionParsing, BitSelectOfNetAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  initial b = w[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->text, "w");
  EXPECT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, PartSelectOfPackedArrayAsOperand) {
  auto r = Parse(
      "module t;\n"
      "  logic [1:0][7:0] arr;\n"
      "  initial x = arr[1][7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, SimpleOperandReplication) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "  initial x = {4{a}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

TEST(OperatorAndExpressionParsing, SimpleOperandSystemFunctionCallPrimary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_TRUE(IsSimpleOperand(rhs));
}

}  // namespace
