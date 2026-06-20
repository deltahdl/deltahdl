#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StreamingOperatorParsing, StreamingWithSliceSize) {
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

TEST(StreamingOperatorParsing, StreamingConcatRightShift) {
  auto r = Parse("module m; initial x = {>> {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->op, TokenKind::kGtGt);
}

TEST(StreamingOperatorParsing, StreamingConcatLeftShift) {
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
TEST(StreamingOperatorParsing, BitStreamCastStreaming) {
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

TEST(StreamingOperatorParsing, StreamingAsAssignmentSource) {
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

TEST(StreamingOperatorParsing, StreamingNestedInStreaming) {
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

TEST(StreamingOperatorParsing, StreamingWithNoSliceSize) {
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

TEST(StreamingOperatorParsing, StreamingSliceSizeSimpleType) {
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

TEST(StreamingOperatorParsing, StreamExpressionWithArrayRange) {
  // §11.4.14 BNF: stream_expression ::= expression [ with [
  // array_range_expression ] ]. Exercises a `with` clause carrying a colon
  // range on the stream element.
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] arr[0:3];\n"
      "  logic [15:0] dst;\n"
      "  initial dst = {>> {arr with [0:1]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_FALSE(rhs->elements.empty());
  EXPECT_NE(rhs->elements[0]->with_expr, nullptr);
}

TEST(StreamingOperatorParsing, StreamExpressionWithPlusColonRange) {
  // §11.4.14 BNF: array_range_expression covers the `+:` form.
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] arr[0:3];\n"
      "  logic [15:0] dst;\n"
      "  initial dst = {>> {arr with [0 +: 2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_FALSE(rhs->elements.empty());
  auto* with = rhs->elements[0]->with_expr;
  ASSERT_NE(with, nullptr);
  EXPECT_TRUE(with->is_part_select_plus);
}

TEST(StreamingOperatorParsing, StreamExpressionWithMinusColonRange) {
  // §11.4.14 BNF: array_range_expression covers the `-:` form.
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] arr[0:3];\n"
      "  logic [15:0] dst;\n"
      "  initial dst = {>> {arr with [3 -: 2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_FALSE(rhs->elements.empty());
  auto* with = rhs->elements[0]->with_expr;
  ASSERT_NE(with, nullptr);
  EXPECT_TRUE(with->is_part_select_minus);
}

TEST(StreamingOperatorParsing, StreamExpressionWithBareIndex) {
  // §11.4.14 BNF: array_range_expression admits a single expression with no
  // colon — the degenerate one-element range form.
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] arr[0:3];\n"
      "  logic [7:0] dst;\n"
      "  initial dst = {>> {arr with [2]}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_FALSE(rhs->elements.empty());
  auto* with = rhs->elements[0]->with_expr;
  ASSERT_NE(with, nullptr);
  EXPECT_FALSE(with->is_part_select_plus);
  EXPECT_FALSE(with->is_part_select_minus);
  EXPECT_EQ(with->index_end, nullptr);
}

}  // namespace
