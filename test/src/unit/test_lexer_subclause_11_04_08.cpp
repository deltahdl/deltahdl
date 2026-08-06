#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(BitwiseOperatorLexing, BinaryAnd) {
  auto tokens = Lex("a & b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kAmp);
}

TEST(BitwiseOperatorLexing, BinaryOr) {
  auto tokens = Lex("a | b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPipe);
}

TEST(BitwiseOperatorLexing, BinaryXor) {
  auto tokens = Lex("a ^ b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kCaret);
}

TEST(BitwiseOperatorLexing, BinaryXnorCaretTilde) {
  auto tokens = Lex("a ^~ b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kCaretTilde);
}

TEST(BitwiseOperatorLexing, BinaryXnorTildeCaret) {
  auto tokens = Lex("a ~^ b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTildeCaret);
}

TEST(BitwiseOperatorLexing, UnaryNot) {
  auto tokens = Lex("~a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
