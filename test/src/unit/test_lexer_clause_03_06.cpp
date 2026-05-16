// §3.6: The checker construct is enclosed by the keywords
// checker ... endchecker.  The lexer must recognise both as distinct
// keyword tokens.

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(CheckerBlockLexing, CheckerKeywordRecognised) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(CheckerBlockLexing, EndcheckerKeywordRecognised) {
  auto r = LexOne("endchecker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndchecker);
}

TEST(CheckerBlockLexing, CheckerEnclosureTokenStream) {
  auto tokens = Lex("checker c; endchecker");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwChecker);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "c");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwEndchecker);
}

}  // namespace
