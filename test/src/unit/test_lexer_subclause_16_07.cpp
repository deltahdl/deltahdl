#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SequenceLexing, HashHashIsCycleDelayOperator) {
  auto tokens = Lex("a ##1 b");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHashHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
}

TEST(SequenceLexing, DelayRangeBracketsTokenize) {
  auto tokens = Lex("##[1:5]");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHashHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBracket);
}

TEST(SequenceLexing, UnboundedDelayRangeUsesDollar) {
  auto tokens = Lex("##[0:$]");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHashHash);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kColon);
  EXPECT_EQ(tokens[4].kind, TokenKind::kDollar);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBracket);
}

TEST(SequenceLexing, RepetitionStarAndPlusTokenize) {
  auto tokens = Lex("[*] [+]");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[1].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[2].kind, TokenKind::kRBracket);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[5].kind, TokenKind::kRBracket);
}

TEST(SequenceLexing, GotoRepetitionUsesArrow) {
  // §16.7 goto_repetition: `[->` opens the form, so the arrow must lex as
  // one token to keep the brackets recognizable as repetition delimiters.
  auto tokens = Lex("[->3]");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[1].kind, TokenKind::kArrow);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBracket);
}

TEST(SequenceLexing, NonconsecutiveRepetitionUsesEquals) {
  // §16.7 nonconsecutive_repetition: `[=N]` shape.
  auto tokens = Lex("[=2]");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kLBracket);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kRBracket);
}

}  // namespace
