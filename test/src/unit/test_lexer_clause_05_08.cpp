#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(TimeLiteralLexing, TimeLiteralS) {
  auto r = LexOne("1s");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1s");
}

TEST(TimeLiteralLexing, TimeLiteralMs) {
  auto r = LexOne("1ms");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ms");
}

TEST(TimeLiteralLexing, TimeLiteralUs) {
  auto r = LexOne("1us");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1us");
}

TEST(TimeLiteralLexing, TimeLiteralNs) {
  auto r = LexOne("1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ns");
}

TEST(TimeLiteralLexing, TimeLiteralPs) {
  auto r = LexOne("1ps");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1ps");
}

TEST(TimeLiteralLexing, TimeLiteralFs) {
  auto r = LexOne("1fs");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "1fs");
}

TEST(TimeLiteralLexing, TimeLiteralFixedPoint) {
  auto r = LexOne("2.1ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r.token.text, "2.1ns");
}

TEST(TimeLiteralLexing, SpaceSeparatesNumberAndUnit) {
  auto tokens = Lex("10 ns");
  ASSERT_GE(tokens.size(), 3u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

TEST(TimeLiteralLexing, NotTimeLiteralIfMoreChars) {
  auto r = LexOne("1nsec ");

  EXPECT_NE(r.token.kind, TokenKind::kTimeLiteral);
}

TEST(TimeLiteralLexing, ExponentFormatIsNotTimeLiteral) {
  auto tokens = Lex("1e3ns");
  ASSERT_GE(tokens.size(), 2u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kRealLiteral);
  EXPECT_EQ(tokens[0].text, "1e3");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "ns");
}

TEST(TimeLiteralLexing, UnlistedSuffixIsNotTimeLiteral) {
  auto tokens = Lex("1cs");
  ASSERT_GE(tokens.size(), 2u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "1");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "cs");
}

}  // namespace
