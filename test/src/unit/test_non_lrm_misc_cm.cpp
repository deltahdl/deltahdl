// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult15 Parse(const std::string& src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult15& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

TEST(ParserSection16, ImmediateAssertPassOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert(valid) $display(\"passed\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_EQ(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — assume
// =============================================================================
TEST(ParserSection16, ImmediateAssumeBasic) {
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

TEST(ParserSection16, ImmediateAssumeWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assume(y > 0) $display(\"ok\"); else $error(\"bad\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssumeImmediate);
  EXPECT_NE(stmt->assert_pass_stmt, nullptr);
  EXPECT_NE(stmt->assert_fail_stmt, nullptr);
}

// =============================================================================
// §16.3 Immediate assertions — cover
// =============================================================================
TEST(ParserSection16, ImmediateCoverBasic) {
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

}  // namespace
