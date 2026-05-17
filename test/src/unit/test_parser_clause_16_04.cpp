#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.4 Syntax 16-2 distinguishes two kinds of deferred immediate assertion:
// observed (assert #0 / assume #0 / cover #0) and final (assert final /
// assume final / cover final). The §16.4 prose then sends the two kinds to
// different regions (Reactive vs Postponed). The parser must therefore
// preserve the kind so later stages can route accordingly.

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

// §16.4 Syntax 16-2: deferred_immediate_assume_statement covers #0 and final.
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

// §16.4 Syntax 16-2: deferred_immediate_cover_statement covers #0 and final.
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

// §16.4 "A deferred assertion may be used as a module_common_item." The
// labeled module-level form (deferred_immediate_assertion_item ::=
// [block_identifier :] deferred_immediate_assertion_statement) must parse
// for all three keywords and both kinds.
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

// §16.4 BNF "deferred_immediate_assert_statement ::= ... assert final
// (expression) action_block". The expression is mandatory; verify the
// parser rejects a missing expression after the `final` keyword.
TEST(DeferredAssertionParsing, FinalAssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4 "Syntax: Deferred assertions use #0 (for an observed deferred
// assertion) or final (for a final deferred assertion) after the
// verification directive." The two markers are mutually exclusive: a
// stray final after #0 is not part of any production.
TEST(DeferredAssertionParsing, Hash0PrecludesFinalKeyword) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 final (1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4: deferred assertions still take a pass action_block + else fail.
// Confirm both branches parse and the final-deferred flag still survives.
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

// §16.4 Syntax 16-2: `deferred_immediate_assert_statement ::= assert #0
// (expression) action_block | ...`. The only legal hash value is 0; any
// other integer literal violates the BNF and must be rejected.
TEST(DeferredAssertionParsing, ProceduralAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #5 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4 Syntax 16-2: same #0-only rule for `assume`.
TEST(DeferredAssertionParsing, ProceduralAssumeNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #3 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4 Syntax 16-2: same #0-only rule for `cover`.
TEST(DeferredAssertionParsing, ProceduralCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #7 (1);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4 Syntax 16-2 + B2 (deferred_immediate_assertion_item): the
// module-level form inherits the deferred_immediate_assertion_statement
// grammar, so `#0` is the only legal hash here too. A `#N` at module
// level must be rejected on the assert/assume path.
TEST(DeferredAssertionParsing, ModuleLevelAssertNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  chk: assert #2 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.4 Syntax 16-2 + B2: same #0-only rule applies to the module-level
// cover path (separate parser branch from the assert/assume item path).
TEST(DeferredAssertionParsing, ModuleLevelCoverNonZeroHashRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic c;\n"
      "  hit: cover #4 (c);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
