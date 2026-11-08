#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

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

TEST(DesignBuildingBlockLexing, SuffixXsLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1xs");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "xs");
}

TEST(DesignBuildingBlockLexing, SuffixSecLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1sec");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "sec");
}

TEST(DesignBuildingBlockLexing, UpperCaseNsLexesAsIntLiteralThenIdentifier) {
  auto tokens = Lex("1NS");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "NS");
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
