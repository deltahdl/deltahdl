#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// Keywords used by §A.6.5 timing-control BNF.

TEST(TimingControlKeywordLexing, RepeatKeyword) {
  auto r = LexOne("repeat");
  EXPECT_EQ(r.token.kind, TokenKind::kKwRepeat);
}

TEST(TimingControlKeywordLexing, WaitKeyword) {
  auto r = LexOne("wait");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWait);
}

TEST(TimingControlKeywordLexing, WaitOrderKeyword) {
  auto r = LexOne("wait_order");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWaitOrder);
}

TEST(TimingControlKeywordLexing, ForkKeyword) {
  auto r = LexOne("fork");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFork);
}

TEST(TimingControlKeywordLexing, DisableKeyword) {
  auto r = LexOne("disable");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDisable);
}

TEST(TimingControlKeywordLexing, ReturnKeyword) {
  auto r = LexOne("return");
  EXPECT_EQ(r.token.kind, TokenKind::kKwReturn);
}

TEST(TimingControlKeywordLexing, BreakKeyword) {
  auto r = LexOne("break");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBreak);
}

TEST(TimingControlKeywordLexing, ContinueKeyword) {
  auto r = LexOne("continue");
  EXPECT_EQ(r.token.kind, TokenKind::kKwContinue);
}

TEST(TimingControlKeywordLexing, IffKeyword) {
  auto r = LexOne("iff");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIff);
}

TEST(TimingControlKeywordLexing, PosedgeKeyword) {
  auto r = LexOne("posedge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPosedge);
}

TEST(TimingControlKeywordLexing, NegedgeKeyword) {
  auto r = LexOne("negedge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwNegedge);
}

TEST(TimingControlKeywordLexing, EdgeKeyword) {
  auto r = LexOne("edge");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEdge);
}

TEST(TimingControlKeywordLexing, OrKeyword) {
  auto r = LexOne("or");
  EXPECT_EQ(r.token.kind, TokenKind::kKwOr);
}

// Operators used by §A.6.5 timing-control BNF.

TEST(TimingControlOperatorLexing, HashAsDelayPrefix) {
  auto tokens = Lex("#5");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHash);
}

TEST(TimingControlOperatorLexing, AtAsEventControlPrefix) {
  auto tokens = Lex("@(posedge clk)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
}

TEST(TimingControlOperatorLexing, ArrowAsBlockingEventTrigger) {
  auto tokens = Lex("-> ev");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kArrow);
}

TEST(TimingControlOperatorLexing, DashGtGtAsNonblockingEventTrigger) {
  auto tokens = Lex("->> ev");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDashGtGt);
}

TEST(TimingControlOperatorLexing, AtStarEventControl) {
  auto tokens = Lex("@*");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
}

TEST(TimingControlOperatorLexing, ArrowVsDashGtGtDisambiguation) {
  auto tokens = Lex("-> ->>");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kArrow);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDashGtGt);
}

}  // namespace
