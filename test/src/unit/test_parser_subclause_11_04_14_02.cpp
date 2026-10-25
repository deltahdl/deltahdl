#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;
namespace {

TEST(StreamReorderingParsing, LeftShiftOperator) {
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

TEST(StreamReorderingParsing, StreamingWithTypeSliceSize) {
  auto r = Parse("module m; initial x = {<< byte {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(StreamReorderingParsing, StreamingWithIntSliceSize) {
  auto r = Parse("module m; initial x = {<< int {a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

TEST(StreamReorderingParsing, StreamingWithExprSliceSize) {
  auto r = Parse("module m; initial x = {<< 4 {a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  ASSERT_NE(stmt->rhs->lhs, nullptr);
}

// §11.4.14.2: a number written as the slice size is a constant expression,
// kept as the literal it is so that its base is read with its digits; a type
// keyword written there is kept as a name.
TEST(StreamReorderingParsing, NumberSliceSizesKeptAsLiterals) {
  auto r = Parse(
      "module m;\n"
      "  initial x = {<< 8'd8 {a}};\n"
      "  initial x = {<< '1 {a}};\n"
      "  initial x = {<< byte {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  const Expr* sized = items[0]->body->rhs->lhs;
  ASSERT_NE(sized, nullptr);
  EXPECT_EQ(sized->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(sized->text, "8'd8");
  const Expr* unbased = items[1]->body->rhs->lhs;
  ASSERT_NE(unbased, nullptr);
  EXPECT_EQ(unbased->kind, ExprKind::kUnbasedUnsizedLiteral);
  const Expr* type = items[2]->body->rhs->lhs;
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->kind, ExprKind::kIdentifier);
  EXPECT_EQ(type->text, "byte");
}

TEST(StreamReorderingParsing, RightShiftOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {a, b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

}  // namespace
