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

// Lexing "int ' (x)" yields the int keyword token, then TokenKind::kApostrophe,
// then TokenKind::kLParen. A.8.4 writes cast ::= casting_type ' ( expression ),
// so the apostrophe and the ( are two separate grammar terminals. §5.3 rules
// that white space "shall be ignored except when they serve to separate other
// lexical tokens", so a space standing between those two terminals separates
// them and carries nothing else.
TEST(PrimaryLexing,
     WhiteSpaceBetweenApostropheAndLParenLexesApostropheThenLParen) {
  auto tokens = Lex("int ' (x)");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInt);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostrophe);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
}

}  // namespace
