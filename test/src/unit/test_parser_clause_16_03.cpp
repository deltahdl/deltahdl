#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(ImmediateAssertionStatementParsing, DeferredAssertHash0SetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, DeferredAssertFinalSetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
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

TEST(ImmediateAssertionStatementParsing, DeferredAssumeHash0SetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, DeferredAssumeFinalSetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, DeferredCoverHash0SetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, DeferredCoverFinalSetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(ImmediateAssertionStatementParsing, LabeledDeferredAssertModuleLevel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  chk: assert #0 (c);\n"
              "endmodule\n"));
}

TEST(ImmediateAssertionStatementParsing, LabeledDeferredCoverModuleLevel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  hit: cover final (c);\n"
              "endmodule\n"));
}

TEST(ImmediateAssertionStatementParsing, CoverWithElseClauseRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1; else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ImmediateAssertionStatementParsing, AssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ImmediateAssertionStatementParsing, AssumeMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ImmediateAssertionStatementParsing, DeferredAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #1 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ImmediateAssertionStatementParsing, DeferredAssumeNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #5 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ImmediateAssertionStatementParsing, DeferredCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #2 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
