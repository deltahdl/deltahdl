#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

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

TEST(ImmediateAssertionStatementParsing, CoverWithElseClauseRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1;\n"
      "  else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "cover has no fail statement", 3, "16.3"));
}

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
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

TEST(ImmediateAssertionStatementParsing, AssumeMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

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

TEST(ImmediateAssertionStatementParsing, MalformedAssertedExprNames16_3) {
  auto r = Parse(
      "module m;\n"
      "  initial assert x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '('", 2, "16.3"));
}

}  // namespace
