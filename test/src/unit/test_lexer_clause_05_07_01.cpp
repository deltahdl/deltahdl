#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(IntegerLiteralLexing, WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, SpaceBreaksNumberIntoTwo) {
  auto tokens = Lex("12 34");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

}
