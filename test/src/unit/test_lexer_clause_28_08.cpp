// §28.8

#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Each bidirectional pass switch keyword must map to its own token kind so
// downstream stages can distinguish conditional from unconditional variants
// and full-strength from resistive variants.
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
  ASSERT_GE(tokens.size(), 8u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTran);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[7].kind, TokenKind::kSemicolon);
}

TEST(BidirectionalSwitchLexing, Tranif1InstantiationTokenSequence) {
  auto tokens = Lex("tranif1 t1(a, b, en);");
  ASSERT_GE(tokens.size(), 10u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTranif1);
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
