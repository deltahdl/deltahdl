#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LetKeywordLexing, LetKeyword) {
  auto r = LexOne("let");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLet);
  EXPECT_EQ(r.token.text, "let");
}

TEST(LetKeywordLexing, LetIsNotIdentifier) {
  auto r = LexOne("let");
  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

TEST(LetKeywordLexing, LetPrefixIsIdentifier) {
  auto r = LexOne("letter");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "letter");
}

TEST(LetKeywordLexing, UntypedKeyword) {
  auto r = LexOne("untyped");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntyped);
  EXPECT_EQ(r.token.text, "untyped");
}

TEST(LetKeywordLexing, UntypedIsNotIdentifier) {
  auto r = LexOne("untyped");
  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

TEST(LetKeywordLexing, UntypedPrefixIsIdentifier) {
  auto r = LexOne("untyped_arg");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "untyped_arg");
}

TEST(LetKeywordLexing, LetDeclTokenSequence) {
  auto tokens = Lex("let f(x) = x;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLet);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "f");
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "x");
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[5].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[6].kind, TokenKind::kIdentifier);
}

TEST(LetKeywordLexing, LetNoArgsTokenSequence) {
  auto tokens = Lex("let addr = base;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLet);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "addr");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "base");
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(LetKeywordLexing, UntypedInLetPortTokenSequence) {
  auto tokens = Lex("let f(untyped a) = a;");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwLet);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kKwUntyped);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "a");
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

}  // namespace
