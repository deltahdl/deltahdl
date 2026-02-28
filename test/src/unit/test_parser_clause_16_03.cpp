// §16.3: Immediate assertions

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Gap-filling tests identified by coverage proof
// =============================================================================
// concurrent_assertion_item ::= [ block_identifier : ]
// concurrent_assertion_statement
TEST(ParserA210, ConcurrentAssertionItem_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always @(posedge clk) begin\n"
              "    my_check: assert(a == b);\n"
              "  end\n"
              "endmodule\n"));
}

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection16, ImmediateCoverWithPass) {
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
  // cover does not have else branch
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// ---------------------------------------------------------------------------
// action_block: statement_or_null | [statement] else statement_or_null
// ---------------------------------------------------------------------------
// §16.3: action_block in immediate assert — pass statement only
TEST(ParserA603, ActionBlockAssertPassOnly) {
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

// §16.3: action_block in immediate assert — pass and else (fail) statement
TEST(ParserA603, ActionBlockAssertPassAndFail) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a) $display(\"pass\"); else $display(\"fail\");\n"
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

// §16.3: action_block with null pass (semicolon), else fail
TEST(ParserA603, ActionBlockAssertNullPassElseFail) {
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
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// §16.3: action_block with null statement (just semicolon, no actions)
TEST(ParserA603, ActionBlockAssertNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
}

// §16.3: action_block in assume statement
TEST(ParserA603, ActionBlockAssume) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume (x) $display(\"ok\"); else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with assert immediate.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithAssertImmediate) {
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
  EXPECT_NE(body->stmts[1]->assert_expr, nullptr);
}

// =============================================================================
// §16.2 Immediate assertions — overview (assert, assume, cover in one module)
// =============================================================================
TEST(ParserSection16, OverviewAllThreeImmediateKinds) {
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
}

TEST(ParserSection16, OverviewAssertWithComplexExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(a inside {1, 2, 3});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
