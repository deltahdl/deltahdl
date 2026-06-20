#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(PrimaryLexing, TimeLiteralUnsignedNumberAndUnit) {
  auto tokens = Lex("10ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeLiteralFixedPointNumberAndUnit) {
  auto tokens = Lex("1.5ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitSeconds) {
  auto tokens = Lex("1s");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitMilliseconds) {
  auto tokens = Lex("1ms");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitMicroseconds) {
  auto tokens = Lex("1us");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitNanoseconds) {
  auto tokens = Lex("1ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitPicoseconds) {
  auto tokens = Lex("1ps");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitFemtoseconds) {
  auto tokens = Lex("1fs");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

}  // namespace
