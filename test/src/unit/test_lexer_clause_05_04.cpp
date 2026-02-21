#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string& src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

// --- §5.4: Comments ---

TEST(LexerCh504, StarsInsideBlockComment) {
  // §5.4: Only */ ends a block comment; lone * does not.
  auto tokens = Lex("a /* ** * *** */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, SlashesInsideBlockComment) {
  // §5.4: // shall not have any special meaning inside a block comment.
  auto tokens = Lex("a /* / // /// */ b");
  ASSERT_EQ(tokens.size(), 3);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerCh504, UnterminatedBlockCommentError) {
  std::string src = "/* no end";
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  lexer.LexAll();
  EXPECT_TRUE(diag.HasErrors());
}
