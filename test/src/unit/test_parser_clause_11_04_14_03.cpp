#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA85, StreamingConcatAsLhsRightShift) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> {a, b}} = 64'hDEADBEEF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->lhs->op, TokenKind::kGtGt);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

TEST(ParserA85, StreamingConcatAsLhsLeftShift) {
  auto r = Parse(
      "module m; logic [7:0] a, b;\n"
      "  initial {<< byte {a, b}} = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->lhs->op, TokenKind::kLtLt);
  ASSERT_NE(stmt->lhs->lhs, nullptr);
}

TEST(ParserA85, StreamingConcatAsLhsWithSliceSize) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> 8 {a}} = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA85, StreamingConcatAsLhsNonblocking) {
  auto r = Parse(
      "module m; logic [7:0] x;\n"
      "  initial {>> {x}} <= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA85, StreamingConcatAsLhsSingleElement) {
  auto r = Parse(
      "module m; logic [15:0] v;\n"
      "  initial {<< 4 {v}} = 16'hABCD;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->lhs->elements.size(), 1u);
}

TEST(ParserA85, StreamingConcatAsLhsFromStreamingRhs) {
  auto r = Parse(
      "module m; logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b}} = {>> {c, d}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
}

}  // namespace
