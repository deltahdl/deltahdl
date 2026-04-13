#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- From test_parser_clause_05_11.cpp ---

TEST(ArrayLiteralParsing, PositionalArrayLiteral) {
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

TEST(ArrayLiteralParsing, NestedMultidimensional) {
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

TEST(ArrayLiteralParsing, ReplicationSingleElement) {
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

TEST(ArrayLiteralParsing, ReplicationMultiElement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a, b;\n"
              "  int arr [0:3];\n"
              "  initial arr = '{2{a, b}};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n[1:2][1:6] = '{2{'{3{4, 5}}}};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, TypePrefixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  initial $display(triple'{0,1,2});\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, IndexKeyWithDefault) {
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

TEST(ArrayLiteralParsing, DefaultOnlyArray) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int arr [0:3] = '{default: 0};\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, ArrayLiteralAssignment) {
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

TEST(ArrayLiteralParsing, SingleElementArray) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:0] = '{42};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(item->init_expr->elements.size(), 1u);
}

TEST(ArrayLiteralParsing, IndexKeyOnly) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2] = '{0: 10, 1: 20, 2: 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(item->init_expr->pattern_keys.size(), 3u);
}

// --- From test_parser_clause_10_09.cpp ---

TEST(AssignmentPatternParsing, TypedefPrefixedArray) {
  auto r = Parse(
      "module m;\n"
      "  typedef int T[3];\n"
      "  T a = T'{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssignmentPatternParsing, AssignmentPatternInArrayDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{0, 1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, ArrayPatternKeyConstExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{0: 8'd1, 1: 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, NestedAssignmentPatterns) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule"));
}

TEST(AssignmentPatternParsing, NestedStructPatternElements) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b;} ab;\n"
      "  ab arr[1:0];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n");
  VerifyNestedPatternElements(r, 2u);
}

TEST(AssignmentPatternParsing, NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b[4];} ab_t;\n"
              "  int a, b, c;\n"
              "  ab_t v1[1:0] [2:0];\n"
              "  initial v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, NestedStructReplication) {
  EXPECT_TRUE(
      ParseOk("module top();\n"
              "  struct {int X,Y,Z;} XYZ = '{3{1}};\n"
              "  typedef struct {int a,b[4];} ab_t;\n"
              "  int a,b,c;\n"
              "  initial begin\n"
              "    ab_t v1[1:0] [2:0];\n"
              "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssignmentPatternParsing, ConstantAssignmentPatternExpression) {
  auto r = Parse(
      "module m;\n"
      "  localparam int arr [3] = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssignmentPatternParsing, LhsTypedPatternExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef byte U[3];\n"
              "  U A;\n"
              "  byte a, b, c;\n"
              "  initial U'{a, b, c} = A;\n"
              "endmodule\n"));
}

TEST(ArrayLiteralParsing, TypeKeyArrayPattern) {
  auto r = Parse(
      "module m;\n"
      "  int arr [0:2] = '{int: 5, default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(item->init_expr->pattern_keys.size(), 2u);
}

}  // namespace
