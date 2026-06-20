#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockLexing, TimeunitLexesAsKeyword) {
  EXPECT_EQ(LexOne("timeunit").token.kind, TokenKind::kKwTimeunit);
}

TEST(DesignBuildingBlockLexing, TimeprecisionLexesAsKeyword) {
  EXPECT_EQ(LexOne("timeprecision").token.kind, TokenKind::kKwTimeprecision);
}

TEST(DesignBuildingBlockLexing, TimeunitKeywordIsCaseSensitive) {
  EXPECT_NE(LexOne("Timeunit").token.kind, TokenKind::kKwTimeunit);
  EXPECT_NE(LexOne("TIMEUNIT").token.kind, TokenKind::kKwTimeunit);
}

TEST(DesignBuildingBlockLexing, TimeprecisionKeywordIsCaseSensitive) {
  EXPECT_NE(LexOne("Timeprecision").token.kind, TokenKind::kKwTimeprecision);
  EXPECT_NE(LexOne("TIMEPRECISION").token.kind, TokenKind::kKwTimeprecision);
}

TEST(DesignBuildingBlockLexing, TimeunitFollowedByTimeLiteral) {
  auto tokens = Lex("timeunit 100ps");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTimeunit);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, TimeunitSlashSeparatorTokenizes) {
  auto tokens = Lex("timeunit 100ps / 10fs");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTimeunit);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[3].kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, TimeprecisionFollowedByTimeLiteral) {
  auto tokens = Lex("timeprecision 1fs");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTimeprecision);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTimeLiteral);
}

}  // namespace
