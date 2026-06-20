#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(OperatorLexing, UnaryPlus) {
  auto tokens = Lex("+a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
}

TEST(OperatorLexing, UnaryMinus) {
  auto tokens = Lex("-a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kMinus);
}

TEST(OperatorLexing, UnaryBang) {
  auto tokens = Lex("!a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kBang);
}

TEST(OperatorLexing, UnaryTilde) {
  auto tokens = Lex("~a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTilde);
}

TEST(OperatorLexing, UnaryAmp) {
  auto tokens = Lex("&a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAmp);
}

TEST(OperatorLexing, UnaryTildeAmp) {
  auto tokens = Lex("~&a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTildeAmp);
}

TEST(OperatorLexing, UnaryPipe) {
  auto tokens = Lex("|a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kPipe);
}

TEST(OperatorLexing, UnaryTildePipe) {
  auto tokens = Lex("~|a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTildePipe);
}

TEST(OperatorLexing, UnaryCaret) {
  auto tokens = Lex("^a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kCaret);
}

TEST(OperatorLexing, UnaryTildeCaret) {
  auto tokens = Lex("~^a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTildeCaret);
}

TEST(OperatorLexing, UnaryCaretTilde) {
  auto tokens = Lex("^~a");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kCaretTilde);
}

TEST(OperatorLexing, BinaryEqEq) {
  auto tokens = Lex("a == b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEq);
}

TEST(OperatorLexing, BinaryBangEq) {
  auto tokens = Lex("a != b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEq);
}

TEST(OperatorLexing, BinaryEqEqEq) {
  auto tokens = Lex("a === b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqEq);
}

TEST(OperatorLexing, BinaryBangEqEq) {
  auto tokens = Lex("a !== b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqEq);
}

TEST(OperatorLexing, BinaryEqEqQuestion) {
  auto tokens = Lex("a ==? b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqQuestion);
}

TEST(OperatorLexing, BinaryBangEqQuestion) {
  auto tokens = Lex("a !=? b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqQuestion);
}

TEST(OperatorLexing, BinaryAmpAmp) {
  auto tokens = Lex("a && b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kAmpAmp);
}

TEST(OperatorLexing, BinaryPipePipe) {
  auto tokens = Lex("a || b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPipePipe);
}

TEST(OperatorLexing, BinaryPower) {
  auto tokens = Lex("a ** b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPower);
}

TEST(OperatorLexing, BinaryLtLt) {
  auto tokens = Lex("a << b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtLt);
}

TEST(OperatorLexing, BinaryGtGt) {
  auto tokens = Lex("a >> b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtGt);
}

TEST(OperatorLexing, BinaryLtLtLt) {
  auto tokens = Lex("a <<< b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtLtLt);
}

TEST(OperatorLexing, BinaryGtGtGt) {
  auto tokens = Lex("a >>> b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtGtGt);
}

TEST(OperatorLexing, BinaryArrow) {
  auto tokens = Lex("a -> b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kArrow);
}

TEST(OperatorLexing, BinaryLtDashGt) {
  auto tokens = Lex("a <-> b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtDashGt);
}

TEST(OperatorLexing, BinaryStar) {
  auto tokens = Lex("a * b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
}

TEST(OperatorLexing, BinarySlash) {
  auto tokens = Lex("a / b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlash);
}

TEST(OperatorLexing, BinaryPercent) {
  auto tokens = Lex("a % b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPercent);
}

TEST(OperatorLexing, BinaryLtEq) {
  auto tokens = Lex("a <= b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
}

TEST(OperatorLexing, BinaryGtEq) {
  auto tokens = Lex("a >= b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtEq);
}

TEST(OperatorLexing, IncOperatorPlusPlus) {
  auto tokens = Lex("a++");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPlus);
}

TEST(OperatorLexing, DecOperatorMinusMinus) {
  auto tokens = Lex("a--");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusMinus);
}

TEST(OperatorLexing, WhitespaceBreaksLtEq) {
  auto tokens = Lex("a < = b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLt);
  EXPECT_NE(tokens[2].kind, TokenKind::kLtEq);
}

TEST(OperatorLexing, WhitespaceBreaksGtEq) {
  auto tokens = Lex("a > = b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGt);
  EXPECT_NE(tokens[2].kind, TokenKind::kGtEq);
}

}  // namespace
