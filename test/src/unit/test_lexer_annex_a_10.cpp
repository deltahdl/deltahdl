#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(TopLevelGrammarLexing, NoSpaceInRealNumber) {
  auto tokens = Lex("3.14");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(TopLevelGrammarLexing, SpaceBreaksRealNumber) {
  auto tokens = Lex("3 .14");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(TopLevelGrammarLexing, NoSpaceInExponentNumber) {
  auto tokens = Lex("1e10");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
}

TEST(TopLevelGrammarLexing, TimeLiteralNoSpace) {
  auto tokens = Lex("10ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(TopLevelGrammarLexing, TimeLiteralAllUnits) {
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

TEST(TopLevelGrammarLexing, TimeLiteralFixedPoint) {
  auto tokens = Lex("1.5ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(TopLevelGrammarLexing, SimpleIdentStartsWithAlpha) {
  auto tokens = Lex("abc");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
}

TEST(TopLevelGrammarLexing, SimpleIdentStartsWithUnderscore) {
  auto tokens = Lex("_foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_foo");
}

TEST(TopLevelGrammarLexing, SimpleIdentSingleChar) {
  auto tokens = Lex("x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(TopLevelGrammarLexing, SpaceSplitsIdentifiers) {
  auto tokens = Lex("foo bar");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "bar");
}

TEST(TopLevelGrammarLexing, SystemIdNoSpaceAfterDollar) {
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(TopLevelGrammarLexing, DollarAloneIsNotSystemId) {
  auto tokens = Lex("$ display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(TopLevelGrammarLexing, SystemIdWithDigitsOk) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(TopLevelGrammarLexing, EofTerminatesStream) {
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[tokens.size() - 1].kind, TokenKind::kEof);
}

TEST(TopLevelGrammarLexing, EmptyInputHasEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

}  // namespace
