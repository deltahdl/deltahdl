// §10.9.1: Array assignment patterns

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — assignment_pattern_expression
TEST(ParserA84, PrimaryAssignmentPattern) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int arr [3] = '{0, 1, 2};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// pattern ::= '{ pattern { , pattern } }
// pattern ::= '{ member_identifier : pattern { , member_identifier : pattern }
// }
// ---------------------------------------------------------------------------
// §12.6: positional assignment pattern in expression context
TEST(ParserA60701, PatternAssignment) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = '{1, 2, 3};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// assignment_pattern ::= '{ constant_expression { expression { , expression } }
// }
// ---------------------------------------------------------------------------
// §10.9.1: replication form of assignment pattern
TEST(ParserA60701, AssignmentPatternReplication) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = '{4{8'd0}};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9.1: replication form with multiple elements
TEST(ParserA60701, AssignmentPatternReplicationMultiElem) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = '{2{a, b}};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: array_pattern_key with constant_expression
TEST(ParserA60701, ArrayPatternKeyConstExpr) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = '{0: 8'd1, 1: 8'd2};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §10.9: replication pattern — AST repeat_count set
TEST(ParserA60701, ReplicationPatternRepeatCount) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    x = '{3{8'd5}};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 1u);
  // The replication element is a kReplicate expression
  auto *rep = rhs->elements[0];
  EXPECT_EQ(rep->kind, ExprKind::kReplicate);
  EXPECT_NE(rep->repeat_count, nullptr);
}

// --- §5.12 Attributes ---
// From test_parser_clause_05.cpp
TEST(ParserCh510, AssignmentPatternPositional_Parse) {
  auto r = Parse("module t;\n"
                 "  initial x = '{1, 2, 3};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
}

// § constant_primary — constant_assignment_pattern_expression
TEST(ParserA84, ConstantPrimaryAssignmentPattern) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    automatic int arr [3] = '{1, 2, 3};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// --- Assignment pattern ---
TEST(ParserSection11, Sec11_1_AssignmentPatternExpression) {
  auto r = Parse("module t;\n"
                 "  int arr[3];\n"
                 "  initial arr = '{1, 2, 3};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}
// --- Test helpers ---
TEST(ParserSection7, AssignmentPatternPositional) {
  auto r = Parse("module t;\n"
                 "  int C[3] = '{10, 20, 30};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_EQ(item->init_expr->kind, ExprKind::kAssignmentPattern);
}

TEST(ParserCh510, AssignmentPattern_IntKey) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef int triple[1:3];\n"
                      "  triple t = '{1:1, default:0};\n"
                      "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_Replication) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int a[1:3] = '{3{1}};\n"
                      "endmodule"));
}

TEST(ParserCh510, AssignmentPattern_NestedReplication) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int n[1:2][1:6] = '{2{'{3{4, 5}}}};\n"
                      "endmodule"));
}

TEST(ParserCh510, StructLiteral_NestedBraces) {
  // ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef struct {int a; shortreal b;} ab;\n"
                      "  ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};\n"
                      "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_Nested) {
  // int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};\n"
                      "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_Simple) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int arr[0:2] = '{10, 20, 30};\n"
                      "endmodule"));
}

TEST(ParserCh511, ArrayLiteral_DefaultValue) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int arr[0:3] = '{default:0};\n"
                      "endmodule"));
}

} // namespace
