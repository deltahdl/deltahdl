#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §11.4.1: SystemVerilog includes the C assignment operators and special
// bitwise assignment operators: +=, -=, *=, /=, %=, &=, |=, ^=, <<=, >>=,
// <<<=, and >>>=.  Each must lex to its own dedicated token (the parser
// dispatches on TokenKind for compound assignment).  The lvalue/rvalue
// must also lex as separate identifier tokens so the parser sees
// `variable_lvalue assignment_operator expression` (§10.4.1
// operator_assignment BNF).

TEST(AssignmentOperatorLexing, PlusEq) {
  auto tokens = Lex("a += 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
}

TEST(AssignmentOperatorLexing, MinusEq) {
  auto tokens = Lex("a -= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinusEq);
}

TEST(AssignmentOperatorLexing, StarEq) {
  auto tokens = Lex("a *= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStarEq);
}

TEST(AssignmentOperatorLexing, SlashEq) {
  auto tokens = Lex("a /= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSlashEq);
}

TEST(AssignmentOperatorLexing, PercentEq) {
  auto tokens = Lex("a %= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPercentEq);
}

TEST(AssignmentOperatorLexing, AmpEq) {
  auto tokens = Lex("a &= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kAmpEq);
}

TEST(AssignmentOperatorLexing, PipeEq) {
  auto tokens = Lex("a |= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPipeEq);
}

TEST(AssignmentOperatorLexing, CaretEq) {
  auto tokens = Lex("a ^= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kCaretEq);
}

TEST(AssignmentOperatorLexing, LtLtEq) {
  auto tokens = Lex("a <<= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtLtEq);
}

TEST(AssignmentOperatorLexing, GtGtEq) {
  auto tokens = Lex("a >>= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtGtEq);
}

TEST(AssignmentOperatorLexing, LtLtLtEq) {
  auto tokens = Lex("a <<<= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtLtLtEq);
}

TEST(AssignmentOperatorLexing, GtGtGtEq) {
  auto tokens = Lex("a >>>= 1");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[1].kind, TokenKind::kGtGtGtEq);
}

// No spaces between the lvalue, operator, and rvalue: all 12 must still
// lex as distinct compound operator tokens, distinct from `=` (kEq) and
// from their binary counterparts (kPlus, kMinus, kLtLt, etc.).
TEST(AssignmentOperatorLexing, NoSpacesAroundOperator) {
  auto tokens = Lex("a+=b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssignmentOperatorLexing, CompoundOpsDistinctFromBinaryCounterparts) {
  auto tokens = Lex("+ += << <<= <<< <<<=");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLtLt);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLtLtEq);
  EXPECT_EQ(tokens[4].kind, TokenKind::kLtLtLt);
  EXPECT_EQ(tokens[5].kind, TokenKind::kLtLtLtEq);
}

}  // namespace
