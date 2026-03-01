// §5.3: White space

#include "fixture_parser.h"

using namespace delta;

namespace {

// =========================================================================
// White space as token delimiter
// =========================================================================
// Tab, newline, and space are all equivalent token delimiters.
TEST(ParserCh501, Sec5_1_WhitespaceTabDelimiter) {
  // Tabs instead of spaces between all tokens.
  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tendmodule"));
}

TEST(ParserCh501, Sec5_1_WhitespaceNewlineDelimiter) {
  // Every token on its own line.
  EXPECT_TRUE(
      ParseOk("module\n"
              "t\n"
              ";\n"
              "logic\n"
              "a\n"
              ";\n"
              "endmodule\n"));
}

TEST(ParserCh501, Sec5_1_WhitespaceSpaceDelimiter) {
  // Single spaces between every token.
  EXPECT_TRUE(ParseOk("module t ; logic a ; endmodule"));
}

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

// =========================================================================
// White space inside string literals is preserved
// =========================================================================
TEST(ParserCh501, Sec5_1_WhitespaceInsideStringPreserved) {
  // Whitespace within a string literal must be preserved, not collapsed.
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"  hello   world  \");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
  // The string text should contain the original whitespace.
  EXPECT_NE(stmt->expr->args[0]->text.find("  hello   world  "),
            std::string_view::npos);
}

// =========================================================================
// Multiple consecutive white space characters
// =========================================================================
TEST(ParserCh501, Sec5_1_MultipleConsecutiveWhitespace) {
  // Multiple spaces, tabs, and newlines between tokens are equivalent to one.
  EXPECT_TRUE(
      ParseOk("module   \t\t   t  \n\n\n ;   logic   a  ;   endmodule"));
}

// =========================================================================
// Empty module with different whitespace patterns
// =========================================================================
TEST(ParserCh501, Sec5_1_EmptyModuleMinimalWhitespace) {
  // Minimal whitespace: only where required to separate keywords.
  EXPECT_TRUE(ParseOk("module t;endmodule"));
}

TEST(ParserCh501, Sec5_1_EmptyModuleExcessiveWhitespace) {
  // Excessive whitespace everywhere around an empty module body.
  EXPECT_TRUE(
      ParseOk("  \t\n  module  \t  t  \n  ;  \n\n\t  endmodule  \n\n  "));
}

}  // namespace
