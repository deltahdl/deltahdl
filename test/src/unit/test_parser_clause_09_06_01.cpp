// §9.6.1: Wait fork statement

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// Section 9.7 -- Fine-grain process control
// =============================================================================
TEST(ParserSection9b, WaitForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

TEST(ParserSection9b, ForkJoinNoneWithWaitFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10 a = 1; end\n"
      "      begin #20 b = 1; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "    $display(\"all done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// ---------------------------------------------------------------------------
// 17. Fork-join_none followed by wait fork
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_ForkJoinNoneThenWaitFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #10 a = 1; end\n"
      "      begin #20 b = 2; end\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kFork);
  EXPECT_EQ(body->stmts[0]->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

}  // namespace
