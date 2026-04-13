#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ArrayLiteralLexing, PositionalArrayLiteralTokens) {
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

TEST(ArrayLiteralLexing, NestedArrayLiteralTokens) {
  auto tokens = Lex("'{'{0,1,2},'{3{4}}}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(ArrayLiteralLexing, ReplicationArrayTokens) {
  auto tokens = Lex("'{3{4}}");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBrace);
}

TEST(ArrayLiteralLexing, IndexKeyDefaultTokens) {
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

TEST(ArrayLiteralLexing, TypePrefixedTokens) {
  auto tokens = Lex("triple'{0,1,2}");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostropheLBrace);
}

TEST(ArrayLiteralLexing, NestedReplicationTokens) {
  auto tokens = Lex("'{2{'{3{4, 5}}}}");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
}

TEST(ArrayLiteralLexing, MultiElementReplicationTokens) {
  auto tokens = Lex("'{2{a, b}}");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRBrace);
  EXPECT_EQ(tokens[7].kind, TokenKind::kRBrace);
}

TEST(ArrayLiteralLexing, TypeKeyInArrayPatternTokens) {
  auto tokens = Lex("'{int: 5, default: 0}");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostropheLBrace);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwInt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kKwDefault);
  EXPECT_EQ(tokens[6].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[8].kind, TokenKind::kRBrace);
}

}  // namespace
