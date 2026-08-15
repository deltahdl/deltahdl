#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DeferredAssertionParsing, Hash0AssertObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalAssertMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, Hash0AssumeObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalAssumeMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, Hash0CoverObservedNotFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, FinalCoverMarksFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertionParsing, ModuleLevelFinalAssertParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  chk: assert final (c);\n"
              "endmodule\n"));
}

TEST(DeferredAssertionParsing, ModuleLevelHash0CoverParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic c;\n"
              "  hit: cover #0 (c);\n"
              "endmodule\n"));
}

TEST(DeferredAssertionParsing, FinalAssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final;\n"
      "endmodule\n");
  // §16.3 owns the parenthesized asserted expression that a deferred assertion
  // shares with the simple immediate form, so the missing '(' is reported
  // there rather than under §16.4.
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ';'", 2, "16.3"));
}

TEST(DeferredAssertionParsing, Hash0PrecludesFinalKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 final (1);\n"
      "endmodule\n");
  // §16.4 admits #0 or final, never both, so after #0 the parser is already
  // reading the asserted expression §16.3 owns and reports the `final` keyword
  // standing where its '(' belongs.
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got 'final'", 2, "16.3"));
}

TEST(DeferredAssertionParsing, FinalAssertWithPassAndFailActions) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1) $info(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_final_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertionParsing, ProceduralAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #5 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #5", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ProceduralAssumeNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #3 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #3", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ProceduralCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #7 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #7", 2, "16.4"));
}

TEST(DeferredAssertionParsing, ModuleLevelAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  chk: assert #2 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #2", 3, "16.4"));
}

TEST(DeferredAssertionParsing, ModuleLevelCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  hit: cover #4 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "deferred immediate assertion requires #0, got #4", 3, "16.4"));
}

}  // namespace
