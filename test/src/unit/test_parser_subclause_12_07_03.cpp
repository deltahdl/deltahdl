#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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

// §12.7.3 — the implicit block a foreach creates is unnamed by default but can
// be named by prefixing the statement with a label; the label attaches to the
// foreach statement itself.
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

// §12.7.3 — a loop-variable slot implicitly declares an index variable, so it
// admits only an identifier; a function call in that position (its closest
// rejected form) is not a valid implicit declaration and is an error.
TEST(LoopSyntaxParsing, ErrorForeachFunctionCallAsLoopVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[f()]) x = 0;\n"
      "  end\n"
      "endmodule\n");
  // Parser::ParseForeachVars takes `f` as the loop variable and stops, so the
  // call's '(' is what stands where §12.7.3 requires the ']'.
  EXPECT_TRUE(ReportedError(r.diags, "expected ']', got '('", 3, "12.7.3"));
}

// §12.7.3 brackets the loop variables of a foreach, so a loop-variable list
// left unclosed is rejected at the token standing where the ']' belongs. The
// report names §12.7.3 rather than the token it wanted, which is what separates
// it from ErrorForeachMissingCloseBracket above: that case reads the same
// source and asks only whether it was rejected.
TEST(ForeachStmt, MalformedLoopVariableListNames12_7_3) {
  auto r = Parse(
      "module m;\n"
      "  initial foreach (arr[i) begin end\n"
      "endmodule\n");
  ASSERT_FALSE(r.diags.empty());
  EXPECT_EQ(r.diags.front().subclause, "12.7.3");
  EXPECT_EQ(r.diags.front().loc.line, 2u);
  EXPECT_EQ(r.diags.front().loc.column, 25u);
}

// Covers Parser::ParseForeachArrayId in src/parser/parser_stmt_loop.cpp, which
// builds the ExprKind::kMemberAccess a dotted foreach array name becomes. It
// assigned no range.start before this commit, so a report standing at the array
// name printed "<unknown location>" instead of a file, line and column. §12.7.3
// writes the array as `ps_or_hierarchical_array_identifier`, a name whose
// leading identifier opens it, so the node begins at `obj`, at column 20 of
// line
// 2. Parser::MakeMemberAccess in src/parser/expr_parser.cpp takes the same
// position for a dotted name written in an expression.
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

}  // namespace
