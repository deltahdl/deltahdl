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

TEST(BnfClarificationLexing, TimeLiteralNoSpace) {
  auto tokens = Lex("10ns");
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

TEST(BnfClarificationLexing, UnbasedUnsizedZeroNoSpace) {
  auto tokens = Lex("'0");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

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

TEST(BnfClarificationLexing, SpaceBreaksTimeLiteral) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

}
