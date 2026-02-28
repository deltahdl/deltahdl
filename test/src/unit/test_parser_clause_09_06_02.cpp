// §9.6.2: Disable statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// disable_statement ::=
//   disable hierarchical_task_identifier ;
//   | disable hierarchical_block_identifier ;
//   | disable fork ;
// ---------------------------------------------------------------------------
// §9.6.2: disable named block
TEST(ParserA605, DisableBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
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
// LRM section 9.3.1 -- Blocks with disable of named block.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithDisableOwnName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_blk\n"
      "    a = 1;\n"
      "    disable my_blk;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "my_blk");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

struct ParseResult9g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9g Parse(const std::string& src) {
  ParseResult9g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 29. Named fork disabled by name
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_NamedForkDisabledByName) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #100 a = 1;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable my_fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  auto* fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisable);
}

}  // namespace
