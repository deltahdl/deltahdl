
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PrimaryParsing, PrimaryAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{0, 1, 2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, PatternAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternReplication) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{4{8'd0}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, AssignmentPatternReplicationMultiElem) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{2{a, b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, ArrayPatternKeyConstExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{0: 8'd1, 1: 8'd2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternParsing, ReplicationPatternRepeatCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = '{3{8'd5}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 1u);

  auto* rep = rhs->elements[0];
  EXPECT_EQ(rep->kind, ExprKind::kReplicate);
  EXPECT_NE(rep->repeat_count, nullptr);
}

TEST(StructureLiteralParsing, AssignmentPatternPositional_Parse) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
}

TEST(PrimaryParsing, ConstantPrimaryAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int arr [3] = '{1, 2, 3};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, AssignmentPatternExpression) {
  auto r = Parse(
      "module t;\n"
      "  int arr[3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(AggregateTypeParsing, AssignmentPatternPositional) {
  auto r = Parse(
      "module t;\n"
      "  int C[3] = '{10, 20, 30};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
}

TEST(StructureLiteralParsing, AssignmentPattern_IntKey) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple[1:3];\n"
              "  triple t = '{1:1, default:0};\n"
              "endmodule"));
}

TEST(StructureLiteralParsing, AssignmentPattern_Replication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a[1:3] = '{3{1}};\n"
              "endmodule"));
}

TEST(StructureLiteralParsing, StructLiteral_NestedBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule"));
}

TEST(NestedBracesArrayOfStructs, NestedBracesArrayOfStructs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; shortreal b;} ab;\n"
              "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
              "endmodule\n"));
}

TEST(ArrayAssignmentPatterns, NestedStructPatternElements) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct {int a; int b;} ab;\n"
      "  ab arr[1:0];\n"
      "  initial arr = '{'{1, 2}, '{3, 4}};\n"
      "endmodule\n");
  VerifyNestedPatternElements(r, 2u);
}

TEST(NestedReplication, NestedReplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct {int a; int b[4];} ab_t;\n"
              "  int a, b, c;\n"
              "  ab_t v1[1:0] [2:0];\n"
              "  initial v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
              "endmodule\n"));
}

TEST(EmptyAssignmentPattern, EmptyAssignmentPattern) {
  auto r = Parse(
      "module m;\n"
      "  initial x = '{};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 0u);
}

TEST(AssignmentPatternReplication, BlockVarDecl_FullStructReplication) {
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

TEST(AssignmentPatternDefault, AssignmentPatternDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial x = '{default: 0};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  std::string expected_keys[] = {"default"};
  VerifyPatternKeys(rhs, expected_keys, std::size(expected_keys));
}

}  // namespace
