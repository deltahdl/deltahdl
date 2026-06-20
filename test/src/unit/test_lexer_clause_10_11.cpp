#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NetAliasingLexing, AliasKeyword) {
  auto r = LexOne("alias");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlias);
}

TEST(NetAliasingLexing, AliasTokenSequence) {
  auto tokens = Lex("alias a = b ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAlias);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(NetAliasingLexing, AliasThreeNetsTokenSequence) {
  auto tokens = Lex("alias a = b = c ;");
  int eq_count = 0;
  for (auto& t : tokens) {
    if (t.kind == TokenKind::kEq) eq_count++;
  }
  EXPECT_EQ(eq_count, 2);
}

TEST(NetAliasingLexing, AliasConcatBitSelectTokenSequence) {
  auto tokens = Lex("alias {a[7:0]} = b ;");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAlias);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBrace);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLBracket);
}

TEST(NetAliasingLexing, AliasPartSelectTokenSequence) {
  auto tokens = Lex("alias W[31:24] = MSB ;");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAlias);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLBracket);
}

}  // namespace
