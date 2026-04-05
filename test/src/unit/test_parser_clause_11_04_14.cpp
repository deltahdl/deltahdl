#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(OperatorAndExpressionParsing, StreamingWithSliceSize) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< 8 {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_NE(rhs->lhs, nullptr);
}

TEST(ConcatenationParsing, StreamingConcatRightShift) {
  auto r = Parse("module m; initial x = {>> {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGt);
}

TEST(OperatorAndExpressionParsing, StreamingConcatLeftShift) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< {a, b}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  EXPECT_EQ(rhs->elements.size(), 2u);
}
TEST(DataTypeParsing, BitStreamCastStreaming) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    byte a;\n"
      "    int b;\n"
      "    b = int'({<< byte {a}});\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OperatorAndExpressionParsing, StreamingAsAssignmentSource) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial dst = {>> {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(OperatorAndExpressionParsing, StreamingAsAssignmentTarget) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial {>> {a, b}} = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

TEST(OperatorAndExpressionParsing, StreamingNestedInStreaming) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  initial b = {>> {{<< {a}}}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kStreamingConcat);
}

TEST(OperatorAndExpressionParsing, StreamingSourceToStreamingTarget) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b}} = {>> {c, d}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

TEST(OperatorAndExpressionParsing, StreamingWithNoSliceSize) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = {<< {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->lhs, nullptr);
}

TEST(OperatorAndExpressionParsing, StreamingSliceSizeSimpleType) {
  auto r = Parse(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial b = {<< shortint {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(OperatorAndExpressionParsing, StreamingSingleElement) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = {>> {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

}  // namespace
