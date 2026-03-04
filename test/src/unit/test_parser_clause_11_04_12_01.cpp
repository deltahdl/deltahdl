// §11.4.12.1: Replication operator

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// ---------------------------------------------------------------------------
// 14. always_comb with replication
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_Replication) {
  auto r = Parse("module m;\n"
                 "  logic sign_bit;\n"
                 "  logic [7:0] extended;\n"
                 "  always_comb extended = {8{sign_bit}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kReplicate);
  EXPECT_NE(item->body->rhs->repeat_count, nullptr);
}
// =========================================================================
// Section 11.4.1 -- Replication operator
// =========================================================================
TEST(ParserSection11, ReplicationCountAndElements) {
  auto r = Parse("module t;\n"
                 "  initial x = {4{a}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(ParserSection11, ReplicationNestedInConcat) {
  auto r = Parse("module t;\n"
                 "  initial x = {b, {3{a, b}}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kReplicate);
}

TEST(ParserSection11, ReplicationMultipleElements) {
  auto r = Parse("module t;\n"
                 "  initial x = {2{a, b, c}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserAnnexA, A8Replication) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}
// --- 24. Blocking assignment with replication: a = {4{b}} ---
TEST(ParserSection10, Sec10_4_1_ReplicationRhs) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] a;\n"
                 "  reg [1:0] b;\n"
                 "  initial begin\n"
                 "    a = {4{b}};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(ConstEval, Replication) {
  EvalFixture f;
  // {4{1'b1}} = 4'b1111 = 15
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

// § constant_multiple_concatenation ::=
//     { constant_expression constant_concatenation }
TEST(ParserA81, ConstantMultipleConcatenation) {
  auto r = Parse("module m;\n"
                 "  parameter P = {4{8'hFF}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// § multiple_concatenation ::= { expression concatenation }
TEST(ParserA81, MultipleConcatenationBasic) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(stmt->rhs->repeat_count, nullptr);
}

TEST(ParserA81, MultipleConcatenationMultipleInner) {
  auto r = Parse("module m; initial x = {2{a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ParserA81, MultipleConcatenationExprCount) {
  auto r = Parse("module m; initial x = {(N+1){a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

// § constant_primary — constant_multiple_concatenation
TEST(ParserA84, ConstantPrimaryMultipleConcatenation) {
  auto r = Parse("module m; parameter int P = {4{4'd1}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kReplicate);
}

// § primary — multiple_concatenation
TEST(ParserA84, PrimaryMultipleConcatenation) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a;\n"
                 "  logic [31:0] b;\n"
                 "  initial b = {4{a}};\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

// --- Replication ---
TEST(ParserSection11, Sec11_1_ReplicateRepeatCountAndElements) {
  auto r = Parse("module t;\n"
                 "  initial x = {3{a, b}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 2u);
}
TEST(ParserSection11, ReplicationOperator) {
  auto r = Parse("module t;\n"
                 "  initial x = {4{a}};\n"
                 "endmodule\n");
  auto *rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

} // namespace
