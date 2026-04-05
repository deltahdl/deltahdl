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

}  // namespace
