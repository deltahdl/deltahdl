#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// --- Left-to-right element list parsing ---

TEST(StreamExpressionConcatParsing, StreamingRightDetails) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {a, b, c}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(StreamExpressionConcatParsing, StreamConcatMultipleElements) {
  auto r = Parse("module m; initial x = {<< {a, b, c}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(StreamExpressionConcatParsing, ElementOrderPreserved) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {alpha, beta, gamma, delta}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_EQ(rhs->elements.size(), 4u);
  EXPECT_EQ(rhs->elements[0]->text, "alpha");
  EXPECT_EQ(rhs->elements[1]->text, "beta");
  EXPECT_EQ(rhs->elements[2]->text, "gamma");
  EXPECT_EQ(rhs->elements[3]->text, "delta");
}

// --- Branch 1: nested streaming_concatenation as stream_expression ---

TEST(StreamExpressionConcatParsing, NestedStreamingConcatParsed) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {{<< {a}}, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->elements[0]->op, TokenKind::kLtLt);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kIdentifier);
}

// --- Branch 1: expression types (literals, identifiers) ---

TEST(StreamExpressionConcatParsing, LiteralElementsParsed) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {8'hAB, 8'hCD}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->elements.size(), 2u);
}

TEST(StreamExpressionConcatParsing, MixedExpressionTypes) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {a, 8'hFF, b + c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->elements[2]->kind, ExprKind::kBinary);
}

}  // namespace
