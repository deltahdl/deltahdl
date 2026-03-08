#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, StreamingLeft) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {<< {a, b, c}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserA81, StreamingWithTypeSliceSize) {
  auto r = Parse("module m; initial x = {<< byte {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(ParserA81, StreamingWithIntSliceSize) {
  auto r = Parse("module m; initial x = {<< int {a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(ParserA81, StreamingWithExprSliceSize) {
  auto r = Parse("module m; initial x = {<< 4 {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(ParserSection11, StreamingWithTypedSlice) {
  auto r = Parse(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  initial b = {<< byte {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
