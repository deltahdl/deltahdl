#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(BuiltinMethodLexing, DotNotationTokens) {
  auto tokens = Lex("arr.size()");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(BuiltinMethodLexing, DotNotationNoParens) {
  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(BuiltinMethodLexing, ChainedDotNotation) {
  auto tokens = Lex("obj.arr.size()");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(BuiltinMethodLexing, MethodWithArgTokens) {
  auto tokens = Lex("q.push_back(8'hAA)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
}

TEST(BuiltinMethodLexing, MethodNameIsIdentifier) {
  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "size");
}

TEST(BuiltinMethodLexing, MethodWithMultipleArgTokens) {
  auto tokens = Lex("q.insert(0, 42)");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[5].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[7].kind, TokenKind::kRParen);
}

}  // namespace
