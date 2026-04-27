#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.8.6: unary_operator — all 11 tokens

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

// §A.8.6: binary_operator — all tokens including multi-char

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

// §A.8.6: inc_or_dec_operator

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

// §A.8.6: disambiguation — multi-char operators not consumed as shorter tokens

TEST(OperatorLexing, PowerNotTwoStars) {
  auto tokens = Lex("a**b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPower);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, CaseEqualityNotTwoEquals) {
  auto tokens = Lex("a===b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, CaseInequalityNotBangPlusEquals) {
  auto tokens = Lex("a!==b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, ArithShiftLeftNotTwoLtLt) {
  auto tokens = Lex("a<<<b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtLtLt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, ArithShiftRightNotTwoGtGt) {
  auto tokens = Lex("a>>>b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtGtGt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, WildcardEqualityNotEqEqPlus) {
  auto tokens = Lex("a==?b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEqEqQuestion);
}

TEST(OperatorLexing, WildcardInequalityNotBangEqPlus) {
  auto tokens = Lex("a!=?b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBangEqQuestion);
}

TEST(OperatorLexing, TildeCaretVsCaretTildeDistinct) {
  auto t1 = Lex("~^");
  auto t2 = Lex("^~");
  ASSERT_GE(t1.size(), 1u);
  ASSERT_GE(t2.size(), 1u);
  EXPECT_EQ(t1[0].kind, TokenKind::kTildeCaret);
  EXPECT_EQ(t2[0].kind, TokenKind::kCaretTilde);
}

TEST(OperatorLexing, PlusPlusNotTwoPlus) {
  auto tokens = Lex("a++b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, MinusMinusNotTwoMinus) {
  auto tokens = Lex("a--b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

// §A.8.6: multi-char operator tokens are atomic. Whitespace separating their
// constituent characters must yield two distinct single-char tokens, not the
// merged operator.

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

TEST(OperatorLexing, WhitespaceBreaksTildeAmp) {
  auto tokens = Lex("a ~ & b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAmp);
}

TEST(OperatorLexing, WhitespaceBreaksTildeCaret) {
  auto tokens = Lex("a ~ ^ b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[2].kind, TokenKind::kCaret);
}

TEST(OperatorLexing, WhitespaceBreaksCaretTilde) {
  auto tokens = Lex("a ^ ~ b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kCaret);
  EXPECT_EQ(tokens[2].kind, TokenKind::kTilde);
}

TEST(OperatorLexing, WhitespaceBreaksPlusPlus) {
  auto tokens = Lex("a + + b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kPlus);
}

TEST(OperatorLexing, WhitespaceBreaksMinusMinus) {
  auto tokens = Lex("a - - b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kMinus);
}

TEST(OperatorLexing, WhitespaceBreaksArrow) {
  auto tokens = Lex("a - > b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kGt);
}

TEST(OperatorLexing, WhitespaceBreaksLtDashGt) {
  auto tokens = Lex("a < - > b");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[3].kind, TokenKind::kGt);
}

// §A.8.6: token-set closure — character pairs not listed as operators must not
// collapse into single tokens.

TEST(OperatorLexing, AdjacentTildesAreSeparate) {
  auto tokens = Lex("~~a");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[1].kind, TokenKind::kTilde);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, AdjacentBangsAreSeparate) {
  auto tokens = Lex("!!a");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kBang);
  EXPECT_EQ(tokens[1].kind, TokenKind::kBang);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

// §A.8.6: greedy maximal-munch keeps the longest §A.8.6 token and leaves the
// remainder for the next token.

TEST(OperatorLexing, GreedyTriplePlusKeepsIncrementThenPlus) {
  auto tokens = Lex("+++a");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlusPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(OperatorLexing, GreedyTripleMinusKeepsDecrementThenMinus) {
  auto tokens = Lex("---a");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kMinusMinus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

}  // namespace
