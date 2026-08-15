#include "fixture_evaluator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

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

// §11.4.12 joins one or more expressions, and an operand may itself be a
// concatenation — the shape the clause illustrates with {b, {3{a, b}}}. This
// covers one nested operand beside a scalar one;
// test_parser_annex_a_08_01.cpp covers a concatenation nested in every operand.
TEST(ConcatenationParsing, ConcatenationNestedInOneOperand) {
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

TEST(ConcatenationParsing, ConcatDistinctFromAssignmentPattern) {
  auto plain = Parse("module m; initial x = {a, b}; endmodule\n");
  ASSERT_NE(plain.cu, nullptr);
  EXPECT_FALSE(plain.has_errors);
  auto* plain_rhs = FirstInitialRHS(plain);
  ASSERT_NE(plain_rhs, nullptr);
  EXPECT_EQ(plain_rhs->kind, ExprKind::kConcatenation);

  auto apos = Parse("module m; initial x = '{a, b}; endmodule\n");
  ASSERT_NE(apos.cu, nullptr);
  EXPECT_FALSE(apos.has_errors);
  auto* apos_rhs = FirstInitialRHS(apos);
  ASSERT_NE(apos_rhs, nullptr);
  EXPECT_EQ(apos_rhs->kind, ExprKind::kAssignmentPattern);
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

// §11.4.12 encloses a concatenation in braces. A concatenation left open is
// rejected at the token standing where the '}' belongs, and the report names
// §11.4.12 rather than the token it wanted.
TEST(Concatenation, MalformedConcatenationNames11_4_12) {
  auto r = Parse(
      "module m;\n"
      "  assign y = {a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '}'", 2, "11.4.12"));
}

}  // namespace
