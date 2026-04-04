#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ConcatenationParsing, ConcatenationInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  always_comb c = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(item->body->rhs->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, ConcatWithPartSelects) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, w, b;\n"
      "  initial x = {a, b[3:0], w, 3'b101};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
}

TEST(OperatorAndExpressionParsing, ConcatPartSelectPostfix) {
  auto r = Parse(
      "module t;\n"
      "  byte a, b;\n"
      "  bit [1:0] c;\n"
      "  initial c = {a + b}[1:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, SelectOnConcatenation) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {a, b}[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(ConcatenationParsing, ConcatenationSingleElement) {
  auto r = Parse("module m; initial x = {a}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 1u);
}

TEST(ConcatenationParsing, ConcatenationTwoElements) {
  auto r = Parse("module m; initial x = {a, b}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

TEST(ConcatenationParsing, ConcatenationThreeElements) {
  auto r = Parse("module m; initial x = {a, b, c}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(ConcatenationParsing, ConcatenationNested) {
  auto r = Parse("module m; initial x = {a, {b, c}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
  EXPECT_EQ(stmt->rhs->elements[1]->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements[1]->elements.size(), 2u);
}

TEST(ConstEval, Concatenation) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4'd3, 4'd5}", f)), 0x35);
}

TEST(ConcatenationParsing, ConcatenationPostfixPartSelect) {
  auto r = Parse("module m; initial x = {a, b}[5:2]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(ConcatenationParsing, ConstantConcatenationInParam) {
  auto r = Parse("module m; parameter int P = {4'd1, 4'd2}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kConcatenation);
}

TEST(OperatorAndExpressionParsing, ConcatenationElements) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {a, b, 1'b0};\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 3u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->elements[2]->kind, ExprKind::kIntegerLiteral);
}

TEST(AssignmentParsing, Concatenation) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a, b, c, d;\n"
      "  initial begin\n"
      "    {a, b} = {c, d};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

}  // namespace
