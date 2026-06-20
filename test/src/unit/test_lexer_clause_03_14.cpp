#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockLexing, AllSixUnitsLexAsTimeLiteral) {
  EXPECT_EQ(LexOne("1s").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ms").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1us").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ns").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1ps").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1fs").token.kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, UnknownSuffixIsNotTimeLiteral) {
  EXPECT_NE(LexOne("1xs").token.kind, TokenKind::kTimeLiteral);
  EXPECT_NE(LexOne("1sec").token.kind, TokenKind::kTimeLiteral);
  EXPECT_NE(LexOne("1NS").token.kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, RangeBoundsAcceptedByLexer) {
  EXPECT_EQ(LexOne("100s").token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(LexOne("1fs").token.kind, TokenKind::kTimeLiteral);
}

TEST(DesignBuildingBlockLexing, NumberAloneIsIntLiteralNotTimeLiteral) {
  EXPECT_EQ(LexOne("1").token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(LexOne("100").token.kind, TokenKind::kIntLiteral);
}

}  // namespace
