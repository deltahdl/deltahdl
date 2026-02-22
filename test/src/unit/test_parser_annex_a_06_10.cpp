#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static ModuleItem *FirstModuleItemOfKind(ParseResult &r, ModuleItemKind kind) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.6.10 Assertion statements — simple_immediate_assert_statement
// =============================================================================

// assert ( expression ) ;
TEST(ParserA610, SimpleAssertSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_expr, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
  EXPECT_FALSE(stmt->is_deferred);
}

// assert ( expression ) pass_stmt ;
TEST(ParserA610, SimpleAssertPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) $display(\"pass\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// assert ( expression ) pass_stmt else fail_stmt ;
TEST(ParserA610, SimpleAssertPassElseFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) $display(\"p\"); else $display(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// assert ( expression ) else fail_stmt ;
TEST(ParserA610, SimpleAssertElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) else $display(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — simple_immediate_assume_statement
// =============================================================================

// assume ( expression ) ;
TEST(ParserA610, SimpleAssumeSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// assume ( expression ) pass else fail ;
TEST(ParserA610, SimpleAssumePassElseFail) {
  auto r = Parse(
      "module m;\n"
      "  initial assume(1) $display(\"p\"); else $display(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — simple_immediate_cover_statement
// =============================================================================

// cover ( expression ) ;
TEST(ParserA610, SimpleCoverSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_EQ(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// cover ( expression ) pass_stmt ;
TEST(ParserA610, SimpleCoverPassAction) {
  auto r = Parse(
      "module m;\n"
      "  initial cover(1) $display(\"hit\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — deferred_immediate_assert_statement
// =============================================================================

// assert #0 ( expression ) ;
TEST(ParserA610, DeferredAssertHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// assert final ( expression ) ;
TEST(ParserA610, DeferredAssertFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assert final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// assert #0 ( expression ) pass else fail ;
TEST(ParserA610, DeferredAssertHash0ActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial assert #0 (1) $display(\"p\"); else $display(\"f\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_TRUE(stmt->is_deferred);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — deferred_immediate_assume_statement
// =============================================================================

// assume #0 ( expression ) ;
TEST(ParserA610, DeferredAssumeHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial assume #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// assume final ( expression ) ;
TEST(ParserA610, DeferredAssumeFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial assume final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// =============================================================================
// A.6.10 — deferred_immediate_cover_statement
// =============================================================================

// cover #0 ( expression ) ;
TEST(ParserA610, DeferredCoverHash0) {
  auto r = Parse(
      "module m;\n"
      "  initial cover #0 (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// cover final ( expression ) ;
TEST(ParserA610, DeferredCoverFinal) {
  auto r = Parse(
      "module m;\n"
      "  initial cover final (1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCoverImmediate);
  EXPECT_TRUE(stmt->is_deferred);
}

// =============================================================================
// A.6.10 — action_block
// =============================================================================

// action_block: begin/end block as pass action
TEST(ParserA610, ActionBlockBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin $display(\"a\"); $display(\"b\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_pass_stmt->kind, StmtKind::kBlock);
}

// action_block: [ statement ] else statement_or_null
TEST(ParserA610, ActionBlockPassFailBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial assert(1) begin end else begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->assert_pass_stmt, nullptr);
  ASSERT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// A.6.10 — concurrent_assertion_statement (module-level)
// =============================================================================

// assert_property_statement
TEST(ParserA610, AssertPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
}

// assume_property_statement
TEST(ParserA610, AssumePropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  assume property (req |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kAssumeProperty);
  ASSERT_NE(item, nullptr);
}

// cover_property_statement
TEST(ParserA610, CoverPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a && b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
}

// cover_sequence_statement
TEST(ParserA610, CoverSequenceModule) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverSequence);
  ASSERT_NE(item, nullptr);
}

// restrict_property_statement
TEST(ParserA610, RestrictPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

// =============================================================================
// A.6.10 — deferred_immediate_assertion_item (module-level)
// =============================================================================

// assert #0 at module level
TEST(ParserA610, DeferredAssertHash0Module) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assert #0 (x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// assert final at module level
TEST(ParserA610, DeferredAssertFinalModule) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assert final (x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.10 — concurrent assertion with action_block
// =============================================================================

// assert property with pass and else actions
TEST(ParserA610, AssertPropertyActionBlock) {
  auto r = Parse(
      "module m;\n"
      "  assert property (a) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kAssertProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
  ASSERT_NE(item->assert_fail_stmt, nullptr);
}

// cover property with pass action only (no else)
TEST(ParserA610, CoverPropertyPassAction) {
  auto r = Parse(
      "module m;\n"
      "  cover property (a) $display(\"covered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstModuleItemOfKind(r, ModuleItemKind::kCoverProperty);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->assert_pass_stmt, nullptr);
}
