#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ScopeResolutionPrefixLexing, TwoComponentPrefixTokens) {
  auto tokens = Lex("pkg::name");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "name");
}

TEST(ScopeResolutionPrefixLexing, ChainedPrefixTokens) {
  auto tokens = Lex("A::B::c");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "A");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "B");
  EXPECT_EQ(tokens[3].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "c");
}

TEST(ScopeResolutionPrefixLexing, PrefixTokensDistinctFromDot) {
  auto dot_tokens = Lex("a.b");
  auto scope_tokens = Lex("a::b");
  ASSERT_GE(dot_tokens.size(), 4u);
  ASSERT_GE(scope_tokens.size(), 4u);
  EXPECT_EQ(dot_tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(scope_tokens[1].kind, TokenKind::kColonColon);
}

}  // namespace
