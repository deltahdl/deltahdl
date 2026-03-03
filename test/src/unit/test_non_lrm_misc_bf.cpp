// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50603& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

namespace {

TEST(ParserCh50601, EscapedIdent_Braces) {
  // \{a,b} is a valid escaped identifier containing braces.
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50602, Keyword_EscapedAsIdentifier) {
  // An escaped keyword should be treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(ParserCh50602, Keyword_AllLowercase) {
  // Keywords are lowercase only; MODULE is not a keyword, so this fails.
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

TEST(ParserCh50603, SystemTask_Display) {
  // $display is a system task call (Section 5.6.3, Section 21.2).
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

}  // namespace
