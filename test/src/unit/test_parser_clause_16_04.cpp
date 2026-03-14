#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- §16.4 Deferred assertions: assert #0 / assert final ---

TEST(DeferredAssertParse, AssertHash0SemicolonOnly) {
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
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertFinalSemicolonOnly) {
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
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertHash0WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (x) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertHash0WithPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (data_ok)\n"
      "      $display(\"pass\"); else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertHash0WithElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (x) else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertFinalWithPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (cond) $display(\"p\"); else $error(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssertHash0ExpressionIsNonNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (a == b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(DeferredAssertParse, AssertHash0NotDeferred) {
  // Simple immediate assert (no #0 / final) should NOT be deferred.
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

// --- §16.4 Deferred assertions: assume #0 / assume final ---

TEST(DeferredAssertParse, AssumeHash0SemicolonOnly) {
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
}

TEST(DeferredAssertParse, AssumeFinalSemicolonOnly) {
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
}

TEST(DeferredAssertParse, AssumeHash0WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume #0 (valid) $display(\"assumed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
}

TEST(DeferredAssertParse, AssumeHash0WithElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume #0 (x) else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(DeferredAssertParse, AssumeFinalWithPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (cond) $display(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// --- §16.4 Deferred assertions: cover #0 / cover final ---

TEST(DeferredAssertParse, CoverHash0SemicolonOnly) {
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
}

TEST(DeferredAssertParse, CoverFinalSemicolonOnly) {
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
}

TEST(DeferredAssertParse, CoverHash0WithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover #0 (x) $display(\"hit\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
}

TEST(DeferredAssertParse, CoverFinalWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (x) $display(\"hit\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
}

TEST(DeferredAssertParse, CoverHash0HasNoElseClause) {
  // Cover uses statement_or_null, not action_block — no else allowed.
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (cond) $display(\"hit\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// --- §16.4 All three kinds together ---

TEST(DeferredAssertParse, AllThreeKindsHash0InSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert #0 (a);\n"
      "    assume #0 (b);\n"
      "    cover #0 (c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 3u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmts[0]->is_deferred);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmts[1]->is_deferred);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmts[2]->is_deferred);
}

TEST(DeferredAssertParse, AllThreeKindsFinalInSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert final (a);\n"
      "    assume final (b);\n"
      "    cover final (c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 3u);
  EXPECT_TRUE(stmts[0]->is_deferred);
  EXPECT_TRUE(stmts[1]->is_deferred);
  EXPECT_TRUE(stmts[2]->is_deferred);
}

// --- §16.4.3 Deferred assertions outside procedural code (module-level) ---

TEST(DeferredAssertParse, AssertHash0ModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(DeferredAssertParse, AssertFinalModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert final (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(DeferredAssertParse, AssumeHash0ModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assume #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(DeferredAssertParse, CoverHash0ModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  cover #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// --- §16.4 Labeled deferred assertions ---

TEST(DeferredAssertParse, LabeledAssertHash0) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  initial begin\n"
               "    my_check: assert #0 (a == b);\n"
               "  end\n"
               "endmodule\n"));
}

TEST(DeferredAssertParse, LabeledAssertFinal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  initial begin\n"
               "    final_check: assert final (x);\n"
               "  end\n"
               "endmodule\n"));
}

// --- §16.4 Deferred assertions in always_comb ---

TEST(DeferredAssertParse, AssertHash0InAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    assert #0 (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  auto* stmt = item->body->stmts[0];
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// --- §16.4 is_final_deferred flag ---

TEST(DeferredAssertParse, AssertHash0IsNotFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, AssertFinalIsFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, AssumeHash0IsNotFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, AssumeFinalIsFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, CoverHash0IsNotFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, CoverFinalIsFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_TRUE(stmt->is_final_deferred);
}

TEST(DeferredAssertParse, SimpleImmediateAssertNotFinalDeferred) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->is_deferred);
  EXPECT_FALSE(stmt->is_final_deferred);
}

// --- §16.4.3 Module-level: assume kind preserved ---

TEST(DeferredAssertParse, AssumeHash0ModuleLevelKind) {
  // Module-level assume #0 must preserve kAssumeImmediate (not kAssertImmediate).
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assume #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindItemByKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(item->body->is_deferred);
}

TEST(DeferredAssertParse, AssumeFinalModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assume final (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(DeferredAssertParse, CoverFinalModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  cover final (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// --- §16.4 Labeled module-level deferred assertions ---

TEST(DeferredAssertParse, LabeledAssertHash0ModuleLevel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  logic a;\n"
               "  a1: assert #0 (a);\n"
               "endmodule\n"));
}

TEST(DeferredAssertParse, LabeledAssertFinalModuleLevel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  logic a;\n"
               "  a2: assert final (a);\n"
               "endmodule\n"));
}

// --- §16.4 Deferred assertions in always_latch ---

TEST(DeferredAssertParse, AssertHash0InAlwaysLatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
               "  logic a;\n"
               "  always_latch begin\n"
               "    assert #0 (a);\n"
               "  end\n"
               "endmodule\n"));
}

// --- §16.4 All three final kinds with actions ---

TEST(DeferredAssertParse, AllThreeFinalKindsWithActions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert final (a) $display(\"p\"); else $error(\"f\");\n"
      "    assume final (b) $display(\"p\"); else $error(\"f\");\n"
      "    cover final (c) $display(\"hit\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 3u);
  EXPECT_TRUE(stmts[0]->is_final_deferred);
  EXPECT_NE(stmts[0]->assert_pass_stmt, nullptr);
  EXPECT_NE(stmts[0]->assert_fail_stmt, nullptr);
  EXPECT_TRUE(stmts[1]->is_final_deferred);
  EXPECT_NE(stmts[1]->assert_pass_stmt, nullptr);
  EXPECT_NE(stmts[1]->assert_fail_stmt, nullptr);
  EXPECT_TRUE(stmts[2]->is_final_deferred);
  EXPECT_NE(stmts[2]->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmts[2]->assert_fail_stmt, nullptr);
}

}  // namespace
