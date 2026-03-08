// Non-LRM tests

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- §5.10: structure literal token recognition ---
TEST(LexerClause05, Cl5_10_ApostropheLBraceToken) {
  auto r = LexOne("'{");
  EXPECT_EQ(r.token.kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_10_PositionalStructLiteralTokens) {
  // '{0, 0.0} — positional form
  auto tokens = Lex("'{0, 0.0}");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_10_NamedMemberTokens) {
  // '{a:0, b:1} — named member form
  auto tokens = Lex("'{a:0, b:1}");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
}

TEST(LexerClause05, Cl5_10_DefaultKeyTokens) {
  // '{default:0} — default form
  auto tokens = Lex("'{default:0}");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwDefault);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_10_NestedBraces) {
  // '{'{1, 1.0}, '{2, 2.0}} — nested struct pattern
  auto tokens = Lex("'{'{1, 1.0}, '{2, 2.0}}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_10_TypePrefixedTokens) {
  // ab'{int:1, shortreal:1.0} — type-prefixed form
  auto tokens = Lex("ab'{int:1, shortreal:1.0}");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwInt);
}

}  // namespace
