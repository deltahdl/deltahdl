#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

TEST(ThisLexer, ThisIsKeyword) {
  auto tokens = Lex("this");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwThis);
  EXPECT_EQ(tokens[0].text, "this");
}

TEST(ThisLexer, ThisIsNotIdentifier) {
  auto tokens = Lex("this");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_NE(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(ThisLexer, ThisKeywordLookup) {
  auto kw = LookupKeyword("this", KeywordVersion::kVer18002005);
  EXPECT_EQ(kw, std::optional(TokenKind::kKwThis));
}

TEST(ThisLexer, ThisDotMemberLexesAsThreeTokens) {
  auto tokens = Lex("this.x");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwThis);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "x");
}

}  // namespace
