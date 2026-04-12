#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ProceduralBlockLexing, InitialKeyword) {
  auto r = LexOne("initial");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInitial);
}

TEST(ProceduralBlockLexing, AlwaysKeyword) {
  auto r = LexOne("always");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlways);
}

TEST(ProceduralBlockLexing, AlwaysCombKeyword) {
  auto r = LexOne("always_comb");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysComb);
}

TEST(ProceduralBlockLexing, AlwaysLatchKeyword) {
  auto r = LexOne("always_latch");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysLatch);
}

TEST(ProceduralBlockLexing, AlwaysFFKeyword) {
  auto r = LexOne("always_ff");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysFF);
}

TEST(ProceduralBlockLexing, FinalKeyword) {
  auto r = LexOne("final");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFinal);
}

TEST(ProceduralBlockLexing, InitialBlockTokenSequence) {
  auto tokens = Lex("initial a = 0 ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwInitial);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(ProceduralBlockLexing, AlwaysCombTokenSequence) {
  auto tokens = Lex("always_comb b = a ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAlwaysComb);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(ProceduralBlockLexing, FinalBlockTokenSequence) {
  auto tokens = Lex("final $display ( \"done\" ) ;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwFinal);
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
}

TEST(ProceduralBlockLexing, CompoundAssignPlusEqTokenSequence) {
  auto tokens = Lex("a += 1 ;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlusEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

TEST(ProceduralBlockLexing, NonblockingAssignTokenSequence) {
  auto tokens = Lex("q <= d ;");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kLtEq);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSemicolon);
}

TEST(ProceduralBlockLexing, AllCompoundAssignOperators) {
  auto tokens = Lex("+= -= *= /= %= &= |= ^= <<= >>= <<<= >>>=");
  int count = 0;
  for (auto& t : tokens) {
    if (t.kind == TokenKind::kPlusEq || t.kind == TokenKind::kMinusEq ||
        t.kind == TokenKind::kStarEq || t.kind == TokenKind::kSlashEq ||
        t.kind == TokenKind::kPercentEq || t.kind == TokenKind::kAmpEq ||
        t.kind == TokenKind::kPipeEq || t.kind == TokenKind::kCaretEq ||
        t.kind == TokenKind::kLtLtEq || t.kind == TokenKind::kGtGtEq ||
        t.kind == TokenKind::kLtLtLtEq || t.kind == TokenKind::kGtGtGtEq) {
      count++;
    }
  }
  EXPECT_EQ(count, 12);
}

}  // namespace
