#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §16.3 "An immediate assertion statement may be an immediate assert, an
// immediate assume, or an immediate cover." The three statement kinds share
// the same syntactic skeleton (action_block / expression / optional label),
// and the §20.10 severity tasks slot into the same action_block — so these
// tests anchor the inter-clause weave at the parser level.

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

// §16.3 "The action_block of an immediate assert or assume statement
// specifies what actions are taken upon success or failure of the assertion.
// The statement associated with success is the first statement... The
// statement associated with else is called the fail statement."
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

// §16.3 "If the pass statement is omitted, then no user-specified action is
// taken..."
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

// §16.3 "A pass statement for an immediate cover may be specified in
// statement_or_null." Cover has no else.
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

// §16.3 "There are two modes of immediate assertions, simple immediate
// assertions and deferred immediate assertions." (Deferred forms use #0 or
// final per the §A.6.10 grammar excerpt.)
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

// §16.3 "The optional statement label (identifier and colon) creates a named
// block around the assertion statement."
TEST(ImmediateAssertionStatementParsing, LabeledAssertParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @* begin chk: assert(c); end\n"
              "endmodule\n"));
}

// §16.3 references §20.10 — "The information about assertion failure can be
// printed using one of the severity system tasks in the action block". Verify
// that the parser accepts §20.10 severity tasks inside the action block.
TEST(ImmediateAssertionStatementParsing, AssertActionBlockAcceptsSeverityTasks) {
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

// §16.3 "If more than one of these system tasks is included in the action
// block, then each shall be executed as specified." Multiple severity tasks
// in a begin/end pass block must parse.
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

// §16.3 "The immediate_assertion_statement is a statement_item and can be
// specified anywhere a procedural statement is specified." Verify the assert
// statement composes inside an always_comb body.
TEST(ImmediateAssertionStatementParsing, AssertInsideAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  always_comb assert(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §16.3 "deferred_immediate_assume_statement ::= assume #0 ( expression )
// action_block | assume final ( expression ) action_block"
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

// §16.3 "deferred_immediate_cover_statement ::= cover #0 ( expression )
// statement_or_null | cover final ( expression ) statement_or_null"
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

// §16.3 "deferred_immediate_assertion_item ::= [ block_identifier : ]
// deferred_immediate_assertion_statement" — module-level labeled form.
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

// §16.3 BNF "simple_immediate_cover_statement ::= cover ( expression )
// statement_or_null" — note the absence of any else branch. The §A.6.10
// grammar excerpt shows action_block (which has else) is only attached to
// assert and assume; cover takes statement_or_null. Parser must reject the
// stray else clause.
TEST(ImmediateAssertionStatementParsing, CoverWithElseClauseRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(c) hit = 1; else miss = 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.3 BNF "simple_immediate_assert_statement ::= assert ( expression )
// action_block" — the expression is mandatory.
TEST(ImmediateAssertionStatementParsing, AssertMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assert();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.3 BNF "simple_immediate_assume_statement ::= assume ( expression )
// action_block" — assume also requires an expression.
TEST(ImmediateAssertionStatementParsing, AssumeMissingExpressionRejected) {
  auto r = Parse(
      "module m;\n"
      "  initial assume();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §16.3 BNF "deferred_immediate_assert_statement ::= assert #0 (expression)
// action_block | assert final (expression) action_block" — the hash form
// accepts only the integer literal 0. Non-zero hash values are rejected.
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
