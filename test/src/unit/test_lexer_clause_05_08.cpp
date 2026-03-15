#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, TimeLiteralS) {
  auto r = LexOne("1s");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1s");
}

TEST(LexicalConventionLexing, TimeLiteralMs) {
  auto r = LexOne("1ms");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ms");
}

TEST(LexicalConventionLexing, TimeLiteralUs) {
  auto r = LexOne("1us");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1us");
}

TEST(LexicalConventionLexing, TimeLiteralNs) {
  auto r = LexOne("1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ns");
}

TEST(LexicalConventionLexing, TimeLiteralPs) {
  auto r = LexOne("1ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ps");
}

TEST(LexicalConventionLexing, TimeLiteralFs) {
  auto r = LexOne("1fs");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1fs");
}

TEST(LexicalConventionLexing, TimeLiteral10ns) {
  auto r = LexOne("10ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "10ns");
}

TEST(LexicalConventionLexing, TimeLiteral100ns) {
  auto r = LexOne("100ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "100ns");
}

TEST(LexicalConventionLexing, TimeLiteral40ps) {
  auto r = LexOne("40ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "40ps");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPoint) {
  auto r = LexOne("2.1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "2.1ns");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPointUs) {
  auto r = LexOne("2.5us");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "2.5us");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPointFs) {
  auto r = LexOne("0.5fs");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "0.5fs");
}

TEST(LexicalConventionLexing, SpaceSeparatesNumberAndUnit) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPointMs) {
  auto r = LexOne("1.5ms");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1.5ms");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPointS) {
  auto r = LexOne("0.001s");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "0.001s");
}

TEST(LexicalConventionLexing, TimeLiteralFixedPointPs) {
  auto r = LexOne("3.7ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "3.7ps");
}

TEST(LexicalConventionLexing, NotTimeLiteralIfMoreChars) {
  auto r = LexOne("1nsec ");

  EXPECT_NE(r.token.kind, TokenKind::kTimeLiteral);
}

}  // namespace
