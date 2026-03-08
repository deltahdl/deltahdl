#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- §5.11: array literal token sequences ---

TEST(LexerClause05, Cl5_11_PositionalArrayLiteralTokens) {
  // '{0, 1, 2} — positional array literal
  auto tokens = Lex("'{0, 1, 2}");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_11_NestedArrayLiteralTokens) {
  // '{'{0,1,2},'{3{4}}} — nested with replication
  auto tokens = Lex("'{'{0,1,2},'{3{4}}}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_11_ReplicationArrayTokens) {
  // '{3{4}} — replication
  auto tokens = Lex("'{3{4}}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

TEST(LexerClause05, Cl5_11_IndexKeyDefaultTokens) {
  // '{1:1, default:0} — index key with default
  auto tokens = Lex("'{1:1, default:0}");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwDefault);
  EXPECT_EQ(tokens[6].kind, TokenKind::kColon);
}

TEST(LexerClause05, Cl5_11_TypePrefixedTokens) {
  // triple'{0,1,2} — type-prefixed array literal
  auto tokens = Lex("triple'{0,1,2}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_10_ReplicationTokens) {
  // '{3{1}} — replication form
  auto tokens = Lex("'{3{1}}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

}  // namespace
