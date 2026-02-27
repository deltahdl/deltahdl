// §5.8: Time literals

#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_parse_314.h"

using namespace delta;

namespace {

// 7. Lexer: all six time suffixes produce kTimeLiteral tokens.
TEST(ParserClause03, Cl3_14_LexerAllTimeSuffixes) {
  auto r_s = LexOne("1s");
  EXPECT_EQ(r_s.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_s.token.text, "1s");
  auto r_ms = LexOne("1ms");
  EXPECT_EQ(r_ms.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ms.token.text, "1ms");
  auto r_us = LexOne("1us");
  EXPECT_EQ(r_us.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_us.token.text, "1us");
  auto r_ns = LexOne("1ns");
  EXPECT_EQ(r_ns.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ns.token.text, "1ns");
  auto r_ps = LexOne("1ps");
  EXPECT_EQ(r_ps.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_ps.token.text, "1ps");
  auto r_fs = LexOne("1fs");
  EXPECT_EQ(r_fs.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r_fs.token.text, "1fs");
}

// 8. Lexer: magnitudes 1, 10, 100 with time suffix.
TEST(ParserClause03, Cl3_14_LexerTimeMagnitudes) {
  auto r1 = LexOne("1ns");
  EXPECT_EQ(r1.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r1.token.text, "1ns");
  auto r10 = LexOne("10ns");
  EXPECT_EQ(r10.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r10.token.text, "10ns");
  auto r100 = LexOne("100ns");
  EXPECT_EQ(r100.token.kind, TokenKind::kTimeLiteral);
  EXPECT_EQ(r100.token.text, "100ns");
}

}  // namespace
