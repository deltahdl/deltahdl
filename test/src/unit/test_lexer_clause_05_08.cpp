#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- §5.8: all six time units ---

TEST(LexerClause05, Cl5_8_TimeLiteralS) {
  auto r = LexOne("1s");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1s");
}

TEST(LexerClause05, Cl5_8_TimeLiteralMs) {
  auto r = LexOne("1ms");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ms");
}

TEST(LexerClause05, Cl5_8_TimeLiteralUs) {
  auto r = LexOne("1us");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1us");
}

TEST(LexerClause05, Cl5_8_TimeLiteralNs) {
  auto r = LexOne("1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ns");
}

TEST(LexerClause05, Cl5_8_TimeLiteralPs) {
  auto r = LexOne("1ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ps");
}

TEST(LexerClause05, Cl5_8_TimeLiteralFs) {
  auto r = LexOne("1fs");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1fs");
}

// --- §5.8: integer format with various magnitudes ---

TEST(LexerClause05, Cl5_8_TimeLiteral10ns) {
  auto r = LexOne("10ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "10ns");
}

TEST(LexerClause05, Cl5_8_TimeLiteral100ns) {
  auto r = LexOne("100ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "100ns");
}

TEST(LexerClause05, Cl5_8_TimeLiteral40ps) {
  auto r = LexOne("40ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "40ps");
}

// --- §5.8: fixed-point format ---

TEST(LexerClause05, Cl5_8_TimeLiteralFixedPoint) {
  auto r = LexOne("2.1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "2.1ns");
}

TEST(LexerClause05, Cl5_8_TimeLiteralFixedPointUs) {
  auto r = LexOne("2.5us");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "2.5us");
}

TEST(LexerClause05, Cl5_8_TimeLiteralFixedPointFs) {
  auto r = LexOne("0.5fs");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "0.5fs");
}

// --- §5.8: no space between number and time unit ---

TEST(LexerClause05, Cl5_8_SpaceSeparatesNumberAndUnit) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);
  // With a space, "10" is a number and "ns" is an identifier
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

// --- §5.8: time literal vs identifier disambiguation ---

TEST(LexerClause05, Cl5_8_NotTimeLiteralIfMoreChars) {
  // "1nsec" should not be time literal; suffix "ns" ends at word boundary
  auto r = LexOne("1nsec ");
  // The lexer should not match "1ns" because "ec" follows without boundary
  EXPECT_NE(r.token.kind, TokenKind::kTimeLiteral);
}

}  // namespace
