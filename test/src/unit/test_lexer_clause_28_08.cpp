

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_gate_instantiation_tokens.h"

using namespace delta;

namespace {

TEST(BidirectionalSwitchLexing, TranKeyword) {
  auto tokens = Lex("tran");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTran);
}

TEST(BidirectionalSwitchLexing, RtranKeyword) {
  auto tokens = Lex("rtran");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRtran);
}

TEST(BidirectionalSwitchLexing, Tranif0Keyword) {
  auto tokens = Lex("tranif0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTranif0);
}

TEST(BidirectionalSwitchLexing, Tranif1Keyword) {
  auto tokens = Lex("tranif1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTranif1);
}

TEST(BidirectionalSwitchLexing, Rtranif0Keyword) {
  auto tokens = Lex("rtranif0");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRtranif0);
}

TEST(BidirectionalSwitchLexing, Rtranif1Keyword) {
  auto tokens = Lex("rtranif1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRtranif1);
}

TEST(BidirectionalSwitchLexing, TranInstantiationTokenSequence) {
  auto tokens = Lex("tran t1(a, b);");
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwTran, 2);
}

TEST(BidirectionalSwitchLexing, Tranif1InstantiationTokenSequence) {
  auto tokens = Lex("tranif1 t1(a, b, en);");
  ExpectNamedGateInstantiation(tokens, TokenKind::kKwTranif1, 3);
}

}  // namespace
