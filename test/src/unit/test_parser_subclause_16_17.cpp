#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ExpectStatementParsing, PassAndElseClause) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect( @(posedge clk) a ##1 b ) ok = 1;\n"
      "    else err = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ExpectStatementParsing, ElseClauseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect( @(posedge clk) a )\n"
      "    else err = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ExpectStatementParsing, NoActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect( @(posedge clk) a ##[1:10] b );\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ExpectStatementParsing, PassStatementOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect( @(posedge clk) a ) ok = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ExpectStatementParsing, NamedPropertyArgument) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, ok;\n"
      "  property p;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "  initial\n"
      "    expect( p ) ok = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ExpectStatementParsing, MissingParenthesesIsAnError) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect a;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 3, "16.17"));
}

void CollectExpects(Stmt* s, std::vector<Stmt*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kExpect) out.push_back(s);
  for (auto* child : s->stmts) CollectExpects(child, out);
  CollectExpects(s->then_branch, out);
  CollectExpects(s->else_branch, out);
  CollectExpects(s->body, out);
  CollectExpects(s->for_body, out);
  for (auto* child : s->fork_stmts) CollectExpects(child, out);
  for (auto& ci : s->case_items) CollectExpects(ci.body, out);
  CollectExpects(s->assert_pass_stmt, out);
  CollectExpects(s->assert_fail_stmt, out);
}

TEST(ExpectStatementParsing, AppearsInAlwaysProcedure) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, ok;\n"
      "  always @(posedge clk)\n"
      "    expect( @(posedge clk) a ) ok = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* always = FirstAlwaysItem(r);
  ASSERT_NE(always, nullptr);
  std::vector<Stmt*> expects;
  CollectExpects(always->body, expects);
  ASSERT_EQ(expects.size(), 1u);
  EXPECT_EQ(expects[0]->kind, StmtKind::kExpect);
  EXPECT_NE(expects[0]->assert_pass_stmt, nullptr);
}

TEST(ExpectStatementParsing, PropertyReferencesAutomaticVariables) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  integer data;\n"
      "  task automatic wait_for(integer value, output bit success);\n"
      "    expect( @(posedge clk) ##[1:10] data == value ) success = 1;\n"
      "    else success = 0;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FirstItem(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  std::vector<Stmt*> expects;
  for (auto* s : task->func_body_stmts) CollectExpects(s, expects);
  ASSERT_EQ(expects.size(), 1u);
  EXPECT_NE(expects[0]->assert_pass_stmt, nullptr);
  EXPECT_NE(expects[0]->assert_fail_stmt, nullptr);
}

}  // namespace
