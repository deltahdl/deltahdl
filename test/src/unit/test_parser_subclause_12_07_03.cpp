#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

TEST(LoopSyntaxParsing, ForeachLoopInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] inv [0:3];\n"
      "  always_comb begin\n"
      "    foreach (arr[i])\n"
      "      inv[i] = ~arr[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* block = FirstAlwaysCombStmt(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->kind, StmtKind::kBlock);
  ASSERT_GE(block->stmts.size(), 1u);
  auto* stmt = block->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_FALSE(stmt->foreach_vars.empty());
}

TEST(LoopSyntaxParsing, ForeachHasExprAndBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) x = arr[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(LoopSyntaxParsing, ForeachWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      $display(\"%d\", arr[i]);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

TEST(LoopSyntaxParsing, ForeachSingleVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

TEST(LoopSyntaxParsing, ForeachMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (matrix[i, j]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(LoopSyntaxParsing, ForeachEmptyVarSlot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[, j]) x = j; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(LoopSyntaxParsing, ForeachHierarchicalArray) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (obj.arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(LoopSyntaxParsing, ForeachThreeDimVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (cube[i, j, k]) x = i + j + k;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 3u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
  EXPECT_EQ(stmt->foreach_vars[2], "k");
}

TEST(LoopSyntaxParsing, ForeachTrailingEmptyVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i, ]) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_TRUE(stmt->foreach_vars[1].empty());
}

TEST(LoopSyntaxParsing, ForeachMiddleEmptyVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i, , k]) x = i + k;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 3u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_TRUE(stmt->foreach_vars[1].empty());
  EXPECT_EQ(stmt->foreach_vars[2], "k");
}

TEST(LoopSyntaxParsing, ErrorForeachMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach arr[i]) x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "12.7.3"));
}

TEST(LoopSyntaxParsing, ErrorForeachMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i] x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 3, "12.7.3"));
}

TEST(LoopSyntaxParsing, ErrorForeachMissingOpenBracket) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr i]) x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '[', got identifier", 3, "12.7.3"));
}

TEST(LoopSyntaxParsing, ErrorForeachMissingCloseBracket) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i) x = i;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got ')'", 3, "12.7.3"));
}

TEST(LoopSyntaxParsing, ForeachCanBeNamedByLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    myloop: foreach (arr[i]) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->label, "myloop");
}

TEST(LoopSyntaxParsing, ErrorForeachFunctionCallAsLoopVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[f()]) x = 0;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got '('", 3, "12.7.3"));
}

TEST(ForeachStmt, MalformedLoopVariableListNames12_7_3) {
  auto r = Parse(
      "module m;\n"
      "  initial foreach (arr[i) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ']'", 2, "12.7.3"));
}

TEST(LoopSyntaxParsing, ForeachArrayNameStartsAtItsRoot) {
  auto r = Parse(
      "module m;\n"
      "  initial foreach (obj.arr[i]) x = i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(stmt->expr->range.start.line, 2u);
  EXPECT_EQ(stmt->expr->range.start.column, 20u);
}

TEST(LoopSyntaxParsing, ForeachArrayMayBeAMemberOfASelectedElement) {
  auto r = Parse(
      "module m;\n"
      "  initial foreach (successors[s]) foreach "
      "(successors[s].m_predecessors[pred]) x = pred;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = FirstInitialStmt(r);
  ASSERT_NE(outer, nullptr);
  ASSERT_EQ(outer->kind, StmtKind::kForeach);
  ASSERT_EQ(outer->foreach_vars.size(), 1u);
  EXPECT_EQ(outer->foreach_vars[0], "s");
  auto* inner = outer->body;
  ASSERT_NE(inner, nullptr);
  ASSERT_EQ(inner->kind, StmtKind::kForeach);
  ASSERT_NE(inner->expr, nullptr);
  ASSERT_EQ(inner->expr->kind, ExprKind::kMemberAccess);
  ASSERT_NE(inner->expr->lhs, nullptr);
  ASSERT_EQ(inner->expr->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(inner->expr->lhs->base, nullptr);
  EXPECT_EQ(inner->expr->lhs->base->kind, ExprKind::kIdentifier);
  EXPECT_EQ(inner->expr->lhs->base->text, "successors");
  ASSERT_NE(inner->expr->lhs->index, nullptr);
  EXPECT_EQ(inner->expr->lhs->index->text, "s");
  ASSERT_NE(inner->expr->rhs, nullptr);
  EXPECT_EQ(inner->expr->rhs->text, "m_predecessors");
  ASSERT_EQ(inner->foreach_vars.size(), 1u);
  EXPECT_EQ(inner->foreach_vars[0], "pred");
}

TEST(LoopSyntaxParsing, ForeachArrayMayBeSelectedThroughThis) {
  auto r = Parse(
      "class C;\n"
      "  function void f();\n"
      "    foreach (this.a[s].b[i, j]) x = i + j;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  auto* method = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(method, nullptr);
  ASSERT_EQ(method->func_body_stmts.size(), 1u);
  auto* stmt = method->func_body_stmts[0];
  ASSERT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_NE(stmt->expr, nullptr);
  ASSERT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(stmt->expr->rhs->text, "b");
  ASSERT_NE(stmt->expr->lhs, nullptr);
  ASSERT_EQ(stmt->expr->lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(stmt->expr->lhs->base->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(stmt->expr->lhs->base->rhs->text, "a");
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

}  // namespace
