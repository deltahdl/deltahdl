#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(UdpInstantiationLexing, BasicInstantiationTokenSequence) {
  auto tokens = Lex("my_udp u1(y, a, b);");
  ASSERT_GE(tokens.size(), 9u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[8].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[9].kind, TokenKind::kSemicolon);
}

TEST(UdpInstantiationLexing, UnnamedInstantiationTokenSequence) {
  auto tokens = Lex("my_udp (y, a);");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
}

TEST(UdpInstantiationLexing, DelayTokenSequence) {
  auto tokens = Lex("my_udp #5 u1(y, a);");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
}

TEST(UdpInstantiationLexing, TwoValueDelayTokenSequence) {
  auto tokens = Lex("my_udp #(3, 5) u1(y, a);");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
}

TEST(UdpInstantiationLexing, DriveStrengthTokenSequence) {
  auto tokens = Lex("my_udp (strong0, weak1) u1(y, a);");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwWeak1);
}

TEST(UdpInstantiationLexing, MultipleInstancesTokenSequence) {
  auto tokens = Lex("my_udp u1(y1, a), u2(y2, b);");
  size_t semicolons = 0;
  for (const auto& t : tokens) {
    if (t.kind == TokenKind::kSemicolon) semicolons++;
  }
  EXPECT_EQ(semicolons, 1u);
}

}  // namespace
