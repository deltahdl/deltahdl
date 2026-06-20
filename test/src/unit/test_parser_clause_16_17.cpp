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

// The fail statement of the action block may be a severity system task call,
// as in the LRM's `else $error(...)` example.
TEST(ExpectStatementParsing, ElseCallsSeverityTask) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    expect( @(posedge clk) a ##1 b ##1 c )\n"
      "    else $error(\"expect failed\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExpect);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
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

}  // namespace
