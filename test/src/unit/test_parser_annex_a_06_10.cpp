#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AssertionStatementSyntaxParsing, AssertSemicolonOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_expr, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
  EXPECT_FALSE(stmt->is_deferred);
}

TEST(AssertionStatementSyntaxParsing, AssertWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) $display(\"pass\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertWithPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) $display(\"ok\"); else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertWithElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) else $error(\"fail\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertExpressionIsNonNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a == 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertWithComplexExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a inside {1, 2, 3});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssertPassWithBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin $display(\"a\"); $display(\"b\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlock);
}

TEST(AssertionStatementSyntaxParsing, AssertPassAndFailBothBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin end else begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->assert_fail_stmt->kind, StmtKind::kBlock);
}

TEST(AssertionStatementSyntaxParsing, AssertInSequentialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    assert (a == 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kAssertImmediate);
}

TEST(AssertionStatementSyntaxParsing, AssertInAlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    assert(a);\n"
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
}

TEST(AssertionStatementSyntaxParsing, AssertWithFunctionCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(myfunc(a, b));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(AssertionStatementSyntaxParsing, LabeledAssert) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    my_check: assert(a == b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(AssertionStatementSyntaxParsing, AssertFailCanBeAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (y == 0) else flag = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt->kind, StmtKind::kBlockingAssign);
}

TEST(AssertionStatementSyntaxParsing, AssertPassCanBeAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (myfunc(a,b)) count1 = count1 + 1; else ->event1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssumeBasicSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssumeWithPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(x) $display(\"ok\"); else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssumeWithElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(x) else $error(\"bad\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AssumeExpressionPresent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(x != 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverBasicSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverWithPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover(hit) $display(\"covered\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverHasNoElseClause) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(cond) $display(\"hit\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, CoverExpressionPresent) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover(cond);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

TEST(AssertionStatementSyntaxParsing, AllThreeKindsInSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a);\n"
      "    assume(b);\n"
      "    cover(c);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto stmts = AllInitialStmts(r);
  ASSERT_GE(stmts.size(), 3u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kAssumeImmediate);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kCoverImmediate);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssertHash0) {
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
}

TEST(AssertionStatementSyntaxParsing, DeferredAssertFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert final (x) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssertHash0PassAndFail) {
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
  EXPECT_TRUE(stmt->is_deferred);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssertHash0ActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1) $display(\"p\"); else $display(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssumeHash0) {
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
}

TEST(AssertionStatementSyntaxParsing, DeferredAssumeFinal) {
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

TEST(AssertionStatementSyntaxParsing, DeferredAssumeHash0WithAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume #0 (valid) $display(\"assumed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionStatementSyntaxParsing, DeferredCoverHash0) {
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
}

TEST(AssertionStatementSyntaxParsing, DeferredCoverFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    cover final (x) $display(\"hit\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssertModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionStatementSyntaxParsing, DeferredAssumeModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assume #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionStatementSyntaxParsing, DeferredCoverModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  cover #0 (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionStatementSyntaxParsing, AssertFinalModuleLevel) {
  auto r = Parse(
      "module top();\n"
      "  logic a = 1;\n"
      "  assert final (a != 0);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

TEST(AssertionStatementSyntaxParsing, AssumeFinalModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  assume final (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, CoverFinalModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  cover final (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredAssertModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  chk: assert #0 (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredAssertFinalModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  chk: assert final (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredAssumeHash0ModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  chk: assume #0 (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredAssumeFinalModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  chk: assume final (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredCoverHash0ModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  hit: cover #0 (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, LabeledDeferredCoverFinalModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  hit: cover final (a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorAssertMissingExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial assert();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorAssertMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  initial assert 1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorAssertMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorAssumeMissingExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial assume();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorCoverMissingExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial cover();\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorCoverWithElseClause) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(1) $display(\"hit\"); else $display(\"miss\");\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, AssumeWithPassActionOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(x) $display(\"ok\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

TEST(AssertionStatementSyntaxParsing, ErrorDeferredAssertHashNonZero) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #1 (a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorDeferredAssumeHashNonZero) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #2 (a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorDeferredCoverHashNonZero) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #3 (a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorDeferredCoverHash0WithElseClause) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1) $display(\"hit\"); else $display(\"miss\");\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(AssertionStatementSyntaxParsing, ErrorDeferredCoverFinalWithElseClause) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1) $display(\"hit\"); else $display(\"miss\");\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
