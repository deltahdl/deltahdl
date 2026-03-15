#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, AttributeStartTokenRecognized) {
  auto r = LexOne("(*");
  EXPECT_EQ(r.token.kind, TokenKind::kAttrStart);
}

TEST(LexicalConventionLexing, AttrStartEndTokens) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, AttrWithValueTokens) {
  auto tokens = Lex("(* depth = 8 *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, MultipleAttrSpecs) {
  auto tokens = Lex("(* full_case, parallel_case *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, DisambiguatesFromMultiply) {
  auto tokens = Lex("(a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(LexicalConventionLexing, DisambiguatesCloseFromMultiplyParen) {
  auto tokens = Lex("a * b)");
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
}

TEST(LexicalConventionLexing, AttrWithStringValue) {
  auto tokens = Lex("(* mode = \"cla\" *)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[3].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, MultipleSeparateInstancesTokens) {
  auto tokens = Lex("(* foo *) (* bar *)");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
  EXPECT_EQ(tokens[3].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, AttrFollowedByMultiply) {
  auto tokens = Lex("(* mark *) a * b");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
  EXPECT_EQ(tokens[4].kind, TokenKind::kStar);
}

TEST(LexicalConventionLexing, AttrWithExprValueTokens) {
  auto tokens = Lex("(* depth = 3 + 1 *)");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kAttrEnd);
}

}  // namespace
