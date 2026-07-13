#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.17 / Syntax 16-20:
//   expect_property_statement ::= expect ( property_spec ) action_block
// The expect statement parses as a procedural statement: the `expect` keyword,
// a parenthesized property spec, and an action block with an optional pass
// statement and an optional else clause.

// Action block carrying both a pass statement and an else (fail) clause.
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

// The pass statement is optional: an action block may carry only the else
// clause that runs on failure.
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

// The whole action block is optional: `expect ( property_spec ) ;` is a
// complete statement with neither a pass statement nor an else clause.
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

// The else clause is optional: an action block may carry only the pass
// statement that runs when the property succeeds.
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

// §16.17: the expect statement's argument may be a named property rather than
// an inline property declaration. Here the parenthesized property_spec is a
// reference to a property declared elsewhere in the module (a §16.12 named
// property), and the expect still parses as an expect statement with a pass
// action.
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

// Error condition: §16.17's syntax parenthesizes the property spec. An expect
// statement whose property is not wrapped in parentheses is rejected.
TEST(ExpectStatementParsing, MissingParenthesesIsAnError) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect a;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Walks a statement subtree and records every expect statement it contains, so
// a test can confirm the expect parsed even when it is nested in a procedural
// context such as an always body or a task body.
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

// §16.17: the expect statement can appear anywhere a wait statement can appear.
// The existing tests place it directly under an initial procedure; here it sits
// inside an always procedure's timing-controlled body, another legal position
// for a blocking statement.
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

// §16.17: because the expect statement is blocking, its property may refer to
// automatic variables as well as static ones. This mirrors the LRM's task
// automatic form, whose property compares a sampled value against the task's
// automatic argument. The expect parses as a statement of the task body.
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
