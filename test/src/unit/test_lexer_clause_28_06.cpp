// §28.6

#include <gtest/gtest.h>
#include "fixture_lexer.h"

using namespace delta;

namespace {

// Each tri-state gate keyword must map to its own token kind so the parser
// can distinguish bufif0 from bufif1 and notif0 from notif1.
TEST(TristateGateLexing, Bufif0Keyword) {
  auto tokens = Lex("bufif0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBufif0);
}

TEST(TristateGateLexing, Bufif1Keyword) {
  auto tokens = Lex("bufif1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBufif1);
}

TEST(TristateGateLexing, Notif0Keyword) {
  auto tokens = Lex("notif0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNotif0);
}

TEST(TristateGateLexing, Notif1Keyword) {
  auto tokens = Lex("notif1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwNotif1);
}

TEST(TristateGateLexing, NamedGateTokenSequence) {
  auto tokens = Lex("bufif0 b1(out, in, en);");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwBufif0);
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

}  // namespace
