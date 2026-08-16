#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ImmediateAssertionStatementParsing, AssertProducesAssertImmediate) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_FALSE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, AssumeProducesAssumeImmediate) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
}

TEST(ImmediateAssertionStatementParsing, CoverProducesCoverImmediate) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
}

TEST(ImmediateAssertionStatementParsing, AssertActionBlockPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(c) pass = 1; else fail = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ImmediateAssertionStatementParsing, AssertElseOnlyOmitsPass) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(c) else fail = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ImmediateAssertionStatementParsing, CoverPassActionOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(ImmediateAssertionStatementParsing, LabeledAssertParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @* begin chk: assert(c); end\n"
              "endmodule\n"));
}

TEST(ImmediateAssertionStatementParsing,
     AssertActionBlockAcceptsSeverityTasks) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(c) $info(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(ImmediateAssertionStatementParsing, AssertActionBlockMultipleSeverity) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(c) begin $info(\"a\"); $warning(\"b\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlock);
}

TEST(ImmediateAssertionStatementParsing, AssertInsideAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  always_comb assert(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.3 Syntax 16-1 ends simple_immediate_cover_statement in
// `statement_or_null` where the assert and assume forms end in `action_block`,
// and `action_block` is the only production carrying `else`. The else stands on
// a line of its own so that the line the assertion names is the else and not
// the cover above it.
TEST(ImmediateAssertionStatementParsing, CoverWithElseClauseRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1;\n"
      "  else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "cover has no fail statement", 3, "16.3"));
}

// One mistake draws one report. The parser reads the else and the statement
// behind it, so nothing is left for the module body to reject a second time
// under §23.2.4. That the pass statement §16.3 does permit is still read is
// ImmediateAssertionStatementParsing.CoverPassActionOnly above.
TEST(ImmediateAssertionStatementParsing, CoverWithElseReportsExactlyOneError) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1;\n"
      "  else miss = 1;\n"
      "endmodule\n");
  ASSERT_TRUE(ReportedError(r.diags, "cover has no fail statement", 3, "16.3"));
  uint32_t errors = 0;
  for (const auto& diag : r.diags) {
    if (diag.severity == DiagSeverity::kError) ++errors;
  }
  EXPECT_EQ(errors, 1U);
}

TEST(ImmediateAssertionStatementParsing, AssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert();\n"
      "endmodule\n");
  // §11.2 owns the report: the empty parentheses fail as a missing expression,
  // and §16.3's own report is the ')' the parser wants after it.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(ImmediateAssertionStatementParsing, AssumeMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume();\n"
      "endmodule\n");
  // §11.2 owns the report: the empty parentheses fail as a missing expression,
  // and §16.3's own report is the ')' the parser wants after it.
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

// §16.3: the fail statement is any legal procedural statement, so it can signal
// a failure to another part of the testbench -- here an event trigger. The
// action block's else arm accepts a `-> ev` statement.
TEST(ImmediateAssertionStatementParsing, AssertFailActionEventTrigger) {
  auto r = Parse(
      "module m;\n"
      "  event ev;\n"
      "  initial assert(c) else -> ev;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt->kind, StmtKind::kEventTrigger);
}

// §16.3: the asserted expression is an ordinary (nontemporal) expression, so a
// function call is an admitted operand form for the condition.
TEST(ImmediateAssertionStatementParsing, AssertConditionFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(f(a, b)) pass = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_expr, nullptr);
  EXPECT_EQ(stmt->assert_expr->kind, ExprKind::kCall);
}

// §16.3, Syntax 16-2: `simple_immediate_assert_statement ::= assert (
// expression ) action_block`, so the asserted expression is parenthesized. The
// report reads `expected '(', got identifier`, a sentence the concurrent
// assertion of §16.14 and the deferred assertion of §16.4 would write in the
// same words; the subclause is what separates the three.
TEST(ImmediateAssertionStatementParsing, MalformedAssertedExprNames16_3) {
  auto r = Parse(
      "module m;\n"
      "  initial assert x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '('", 2, "16.3"));
}

}  // namespace
