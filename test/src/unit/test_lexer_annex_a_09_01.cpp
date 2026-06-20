#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(AttributeTokenLexing, AttrStartToken) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
}

TEST(AttributeTokenLexing, AttrEndToken) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, AttrStartNotParenStar) {
  auto tokens = Lex("(* x *)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_NE(tokens[0].kind, TokenKind::kLParen);
}

TEST(AttributeTokenLexing, AttrWithMultipleSpecs) {
  auto tokens = Lex("(* a, b *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, AttrWithValue) {
  auto tokens = Lex("(* depth = 4 *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "depth");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, AttrStartNoSpaceBetweenParenStar) {
  auto tokens = Lex("(*foo*)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, ParenStarParenNotAttribute) {
  auto tokens = Lex("(a * b)");
  EXPECT_NE(tokens[0].kind, TokenKind::kAttrStart);
}

TEST(AttributeTokenLexing, AttrWithStringValue) {
  auto tokens = Lex("(* mode = \"cla\" *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[3].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, AttrWithExprValueTokens) {
  auto tokens = Lex("(* depth = 3 + 1 *)");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, AttrNameEscapedIdentifierToken) {
  auto tokens = Lex("(* \\multi-word-name *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "multi-word-name");
}

}  // namespace
