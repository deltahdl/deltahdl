#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

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

TEST(LexerClause05, Cl5_8_SpaceSeparatesNumberAndUnit) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

TEST(LexerClause05, Cl5_8_NotTimeLiteralIfMoreChars) {
  auto r = LexOne("1nsec ");

  EXPECT_NE(r.token.kind, TokenKind::kTimeLiteral);
}

}
