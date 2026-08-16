#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockLexing, TimeunitLexesAsKeyword) {
  EXPECT_EQ(LexOne("timeunit").token.kind, TokenKind::kKwTimeunit);
}

TEST(DesignBuildingBlockLexing, TimeprecisionLexesAsKeyword) {
  EXPECT_EQ(LexOne("timeprecision").token.kind, TokenKind::kKwTimeprecision);
}

// §5.6 rules that identifiers are case sensitive and §5.6.2 that all keywords
// are defined in lowercase only, so `Timeunit` and `TIMEUNIT` are identifiers.
// This fails if the lexer returns any other kind for either of them, and it
// fails if the token text is not the source spelled as it was written.
TEST(DesignBuildingBlockLexing, TimeunitKeywordIsCaseSensitive) {
  auto capitalized = LexOne("Timeunit");
  EXPECT_EQ(capitalized.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(capitalized.token.text, "Timeunit");
  auto uppercase = LexOne("TIMEUNIT");
  EXPECT_EQ(uppercase.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(uppercase.token.text, "TIMEUNIT");
}

// The same two rules of §5.6 and §5.6.2 over `timeprecision`. This fails if the
// lexer returns any kind other than an identifier for `Timeprecision` or
// `TIMEPRECISION`, and it fails if either token's text is not the source
// spelled as it was written.
TEST(DesignBuildingBlockLexing, TimeprecisionKeywordIsCaseSensitive) {
  auto capitalized = LexOne("Timeprecision");
  EXPECT_EQ(capitalized.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(capitalized.token.text, "Timeprecision");
  auto uppercase = LexOne("TIMEPRECISION");
  EXPECT_EQ(uppercase.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(uppercase.token.text, "TIMEPRECISION");
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
