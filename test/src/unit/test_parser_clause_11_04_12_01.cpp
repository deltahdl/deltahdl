#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessParsing, Replication) {
  auto r = Parse(
      "module m;\n"
      "  logic sign_bit;\n"
      "  logic [7:0] extended;\n"
      "  always_comb extended = {8{sign_bit}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kReplicate);
  EXPECT_NE(item->body->rhs->repeat_count, nullptr);
}

TEST(OperatorAndExpressionParsing, ReplicationCountAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {4{a}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 1u);
}

TEST(OperatorAndExpressionParsing, ReplicationNestedInConcat) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {b, {3{a, b}}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kReplicate);
}

TEST(OperatorAndExpressionParsing, ReplicationMultipleElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {2{a, b, c}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(FormalSyntaxParsing, Replication) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(AssignmentParsing, ReplicationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a;\n"
      "  reg [1:0] b;\n"
      "  initial begin\n"
      "    a = {4{b}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(ConstEval, Replication) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

TEST(ConcatenationParsing, ConstantMultipleConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  parameter P = {4{8'hFF}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConcatenationParsing, MultipleConcatenationBasic) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(stmt->rhs->repeat_count, nullptr);
}

TEST(ConcatenationParsing, MultipleConcatenationMultipleInner) {
  auto r = Parse("module m; initial x = {2{a, b}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ConcatenationParsing, MultipleConcatenationExprCount) {
  auto r = Parse("module m; initial x = {(N+1){a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(PrimaryParsing, ConstantPrimaryMultipleConcatenation) {
  auto r = Parse("module m; parameter int P = {4{4'd1}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kReplicate);
}

TEST(PrimaryParsing, PrimaryMultipleConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {4{a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

TEST(OperatorAndExpressionParsing, ReplicateRepeatCountAndElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {3{a, b}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->repeat_count, nullptr);
  EXPECT_EQ(rhs->repeat_count->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->elements.size(), 2u);
}
TEST(OperatorAndExpressionParsing, ReplicationOperator) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {4{a}};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kReplicate);
}

}  // namespace
