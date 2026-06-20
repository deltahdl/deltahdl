#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NamedEventWaitLexer, AtOperatorTokenizes) {
  auto r = LexOne("@");
  EXPECT_EQ(r.token.kind, TokenKind::kAt);
}

TEST(NamedEventWaitLexer, BareWaitFormTokenizes) {
  auto tokens = Lex("@ev");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ev");
}

TEST(NamedEventWaitLexer, ParenthesizedWaitFormTokenizes) {
  auto tokens = Lex("@(ev);");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ev");
  EXPECT_EQ(tokens[3].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(NamedEventWaitLexer, HierarchicalWaitFormTokenizes) {
  auto tokens = Lex("@c1.ev;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "c1");
  EXPECT_EQ(tokens[2].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "ev");
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(NamedEventWaitLexer, WaitAndTriggerOperatorsTokenize) {
  auto tokens = Lex("@ev; ->ev;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ev");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[3].kind, TokenKind::kArrow);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].text, "ev");
  EXPECT_EQ(tokens[5].kind, TokenKind::kSemicolon);
}

}  // namespace
