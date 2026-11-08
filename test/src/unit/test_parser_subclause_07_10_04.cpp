#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(QueueAssignParsing, ConcatAppendHasTwoItems) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {q, 6};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->text, "q");
}

TEST(QueueAssignParsing, ConcatPrependKeepsItemOrder) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int e;\n"
      "  initial q = {e, q};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->text, "e");
}

TEST(QueueAssignParsing, BareSliceCarriesBothBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_NE(rhs->index_end, nullptr);
}

TEST(QueueAssignParsing, DollarBoundIsNamedDollar) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->text, "$");
}

TEST(QueueAssignParsing, DollarMinusOneBoundIsBinary) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = q[0:$-1];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_EQ(rhs->index_end->kind, ExprKind::kBinary);
}

TEST(QueueAssignParsing, SliceInsideBracesStaysASelect) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int e, pos;\n"
      "  initial q = {q[0:pos-1], e, q[pos:$]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kSelect);
}

TEST(QueueAssignParsing, EmptyConcatHasNoItems) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_TRUE(rhs->elements.empty());
}

TEST(QueueAssignParsing, NonblockingBareSliceCarriesBothBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q <= q[1:$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->index_end, nullptr);
}

}  // namespace
