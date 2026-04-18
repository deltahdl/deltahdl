// §28.5

#include <gtest/gtest.h>
#include "fixture_lexer.h"

using namespace delta;

namespace {

// The two multiple-output logic gate keywords must each lex to their own
// distinct token kind so downstream stages can tell buf from not.
TEST(BufNotLexing, BufKeyword) {
  auto tokens = Lex("buf");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBuf);
}

TEST(BufNotLexing, NotKeyword) {
  auto tokens = Lex("not");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNot);
}

TEST(BufNotLexing, NamedBufGateTokenSequence) {
  auto tokens = Lex("buf b1(out, in);");
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBuf);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[7].kind, TokenKind::kSemicolon);
}

}  // namespace
