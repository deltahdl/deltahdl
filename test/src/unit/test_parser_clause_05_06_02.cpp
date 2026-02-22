#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- §5.6.2 Keywords ---

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
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
