

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(GateStrengthLexing, DriveStrengthTokenSequence) {
  auto tokens = Lex("and (strong0, weak1) g1(y, a, b);");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAnd);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kKwStrong0);
  EXPECT_EQ(tokens[3].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[4].kind, TokenKind::kKwWeak1);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRParen);
}

TEST(GateStrengthLexing, AllStrength0Keywords) {
  auto t_supply = Lex("supply0");
  ASSERT_GE(t_supply.size(), 1u);
  EXPECT_EQ(t_supply[0].kind, TokenKind::kKwSupply0);
  auto t_strong = Lex("strong0");
  ASSERT_GE(t_strong.size(), 1u);
  EXPECT_EQ(t_strong[0].kind, TokenKind::kKwStrong0);
  auto t_pull = Lex("pull0");
  ASSERT_GE(t_pull.size(), 1u);
  EXPECT_EQ(t_pull[0].kind, TokenKind::kKwPull0);
  auto t_weak = Lex("weak0");
  ASSERT_GE(t_weak.size(), 1u);
  EXPECT_EQ(t_weak[0].kind, TokenKind::kKwWeak0);
  auto t_highz = Lex("highz0");
  ASSERT_GE(t_highz.size(), 1u);
  EXPECT_EQ(t_highz[0].kind, TokenKind::kKwHighz0);
}

TEST(GateStrengthLexing, AllStrength1Keywords) {
  auto t_supply = Lex("supply1");
  ASSERT_GE(t_supply.size(), 1u);
  EXPECT_EQ(t_supply[0].kind, TokenKind::kKwSupply1);
  auto t_strong = Lex("strong1");
  ASSERT_GE(t_strong.size(), 1u);
  EXPECT_EQ(t_strong[0].kind, TokenKind::kKwStrong1);
  auto t_pull = Lex("pull1");
  ASSERT_GE(t_pull.size(), 1u);
  EXPECT_EQ(t_pull[0].kind, TokenKind::kKwPull1);
  auto t_weak = Lex("weak1");
  ASSERT_GE(t_weak.size(), 1u);
  EXPECT_EQ(t_weak[0].kind, TokenKind::kKwWeak1);
  auto t_highz = Lex("highz1");
  ASSERT_GE(t_highz.size(), 1u);
  EXPECT_EQ(t_highz[0].kind, TokenKind::kKwHighz1);
}

}  // namespace
