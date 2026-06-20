

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

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
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwBufif0, 3);
}

}  // namespace
