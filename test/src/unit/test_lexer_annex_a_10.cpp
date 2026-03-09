#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerA10, NoSpacesInDecimalNumber) {
  auto tokens = Lex("123");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(LexerA10, SpaceBreaksNumberIntoTwo) {
  auto tokens = Lex("12 34");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(LexerA10, NoSpaceInSizedNumber) {
  auto tokens = Lex("8'hFF");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(LexerA10, UnderscoreInNumberOk) {
  auto tokens = Lex("32'hDEAD_BEEF");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(LexerA10, NoSpaceInRealNumber) {
  auto tokens = Lex("3.14");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(LexerA10, SpaceBreaksRealNumber) {
  auto tokens = Lex("3 .14");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(LexerA10, NoSpaceInExponentNumber) {
  auto tokens = Lex("1e10");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(LexerA10, TimeLiteralNoSpace) {
  auto tokens = Lex("10ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(LexerA10, TimeLiteralAllUnits) {
  auto t_s = Lex("1s");
  auto t_ms = Lex("1ms");
  auto t_us = Lex("1us");
  auto t_ns = Lex("1ns");
  auto t_ps = Lex("1ps");
  auto t_fs = Lex("1fs");
  EXPECT_EQ(t_s[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t_ms[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t_us[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t_ns[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t_ps[0].kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(t_fs[0].kind, TokenKind::kTimeLiteral);
}

TEST(LexerA10, TimeLiteralFixedPoint) {
  auto tokens = Lex("1.5ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(LexerA10, UnbasedUnsizedNoSpace) {
  auto tokens = Lex("'0");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerA10, UnbasedUnsizedOneNoSpace) {
  auto tokens = Lex("'1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerA10, UnbasedUnsizedXNoSpace) {
  auto tokens = Lex("'x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerA10, UnbasedUnsizedZNoSpace) {
  auto tokens = Lex("'z");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerA10, SimpleIdentStartsWithAlpha) {
  auto tokens = Lex("abc");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
}

TEST(LexerA10, SimpleIdentStartsWithUnderscore) {
  auto tokens = Lex("_foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_foo");
}

TEST(LexerA10, SimpleIdentSingleChar) {
  auto tokens = Lex("x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(LexerA10, SpaceSplitsIdentifiers) {
  auto tokens = Lex("foo bar");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar");
}

TEST(LexerA10, SystemIdNoSpaceAfterDollar) {
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(LexerA10, DollarAloneIsNotSystemId) {
  auto tokens = Lex("$ display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(LexerA10, SystemIdWithDigitsOk) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(LexerA10, EofTerminatesStream) {
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[tokens.size() - 1].kind, TokenKind::kEof);
}

TEST(LexerA10, EmptyInputHasEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

}  // namespace
