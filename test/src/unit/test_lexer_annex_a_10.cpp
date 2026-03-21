#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(BnfClarificationLexing, NoSpaceInRealNumber) {
  auto tokens = Lex("3.14");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(BnfClarificationLexing, SpaceBreaksRealNumber) {
  auto tokens = Lex("3 .14");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(BnfClarificationLexing, NoSpaceInExponentNumber) {
  auto tokens = Lex("1e10");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(BnfClarificationLexing, TimeLiteralNoSpace) {
  auto tokens = Lex("10ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(BnfClarificationLexing, TimeLiteralAllUnits) {
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

TEST(BnfClarificationLexing, TimeLiteralFixedPoint) {
  auto tokens = Lex("1.5ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(BnfClarificationLexing, SimpleIdentStartsWithAlpha) {
  auto tokens = Lex("abc");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
}

TEST(BnfClarificationLexing, SimpleIdentStartsWithUnderscore) {
  auto tokens = Lex("_foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_foo");
}

TEST(BnfClarificationLexing, SimpleIdentSingleChar) {
  auto tokens = Lex("x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(BnfClarificationLexing, SpaceSplitsIdentifiers) {
  auto tokens = Lex("foo bar");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar");
}

TEST(BnfClarificationLexing, SystemIdNoSpaceAfterDollar) {
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(BnfClarificationLexing, DollarAloneIsNotSystemId) {
  auto tokens = Lex("$ display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(BnfClarificationLexing, SystemIdWithDigitsOk) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(BnfClarificationLexing, EofTerminatesStream) {
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[tokens.size() - 1].kind, TokenKind::kEof);
}

TEST(BnfClarificationLexing, EmptyInputHasEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// Item 53: apostrophe in unbased_unsized_literal not followed by white_space

TEST(BnfClarificationLexing, UnbasedUnsizedZeroNoSpace) {
  auto tokens = Lex("'0");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(BnfClarificationLexing, UnbasedUnsizedOneNoSpace) {
  auto tokens = Lex("'1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(BnfClarificationLexing, UnbasedUnsizedXNoSpace) {
  auto tokens = Lex("'x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(BnfClarificationLexing, UnbasedUnsizedZNoSpace) {
  auto tokens = Lex("'z");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

// Item 38: embedded spaces — space breaks based number

TEST(BnfClarificationLexing, SpaceBreaksBasedNumber) {
  auto tokens = Lex("4 'b1010");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4");
}

TEST(BnfClarificationLexing, NoSpaceInBasedNumber) {
  auto tokens = Lex("4'b1010");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

// Item 49: space after number breaks time literal

TEST(BnfClarificationLexing, SpaceBreaksTimeLiteral) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

}  // namespace
