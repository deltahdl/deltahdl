#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, PositionalArrayLiteral) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2] = '{10, 20, 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(item->init_expr->elements.size(), 3u);
  EXPECT_TRUE(item->init_expr->pattern_keys.empty());
}

TEST(LexicalConventionParsing, NestedMultidimensional) {
  auto r = Parse(
      "module m;\n"
      "  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(item->init_expr->elements.size(), 2u);
  EXPECT_EQ(item->init_expr->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(item->init_expr->elements[1]->kind, ExprKind::kAssignmentPattern);
}

TEST(LexicalConventionParsing, ReplicationSingleElement) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{3{1}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(stmt->rhs->elements.size(), 1u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kReplicate);
  EXPECT_NE(stmt->rhs->elements[0]->repeat_count, nullptr);
}

TEST(LexicalConventionParsing, ReplicationMultiElement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a, b;\n"
              "  int arr [0:3];\n"
              "  initial arr = '{2{a, b}};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:6] = '{2{'{3{4, 5}}}};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, TypePrefixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  initial $display(triple'{0,1,2});\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, IndexKeyWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  typedef int triple [1:3];\n"
      "  triple b = '{1:1, default:0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(item->init_expr->pattern_keys.size(), 2u);
}

TEST(LexicalConventionParsing, DefaultOnlyArray) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:3] = '{default: 0};\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, ArrayLiteralAssignment) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2];\n"
      "  initial arr = '{0, 1, 2};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

}  // namespace
