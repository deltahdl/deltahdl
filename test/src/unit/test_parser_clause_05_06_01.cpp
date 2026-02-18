#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- §5.6.1 Escaped identifiers ---

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// From test_parser_clause_05.cpp

TEST(ParserCh50601, EscapedIdentifierAsName) {
  // §5.6.1: escaped identifiers include special characters.
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserCh50601, EscapedKeywordAsIdentifier) {
  // §5.6.1: escaped keyword is treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

// From test_parser_clause_05b.cpp

TEST(ParserCh50601, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Keyword) {
  // An escaped keyword is treated as a user-defined identifier, not as a
  // keyword. \net is a valid user-defined wire name.
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_SpecialChars) {
  // Escaped identifiers can contain any printable ASCII character.
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_ForwardSlash) {
  // \net1/\net2 is a valid escaped identifier containing a slash.
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Braces) {
  // \{a,b} is a valid escaped identifier containing braces.
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}
