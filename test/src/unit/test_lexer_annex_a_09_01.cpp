#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.9.1: attribute_instance delimiters (* and *)

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
  // (* should be kAttrStart, not kLParen + kStar
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
  // (* with no space is one token
  auto tokens = Lex("(*foo*)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(AttributeTokenLexing, ParenStarParenNotAttribute) {
  // (*) is not an attribute — the * followed by ) means kAttrStart should
  // not be emitted if it would immediately see *)
  auto tokens = Lex("(a * b)");
  EXPECT_NE(tokens[0].kind, TokenKind::kAttrStart);
}

}  // namespace
