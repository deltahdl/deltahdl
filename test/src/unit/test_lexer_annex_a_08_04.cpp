#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §A.8.4 time_literal ::=
//     unsigned_number time_unit
//   | fixed_point_number time_unit
// — the lexer must produce a single kTimeLiteral token for the unsigned
// integer form joined to a time_unit suffix.
TEST(PrimaryLexing, TimeLiteralUnsignedNumberAndUnit) {
  auto tokens = Lex("10ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

// §A.8.4 time_literal — the fixed_point_number form.
TEST(PrimaryLexing, TimeLiteralFixedPointNumberAndUnit) {
  auto tokens = Lex("1.5ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

// §A.8.4 time_unit ::= s | ms | us | ns | ps | fs — each alternative must
// lex into a single kTimeLiteral token when prefixed by an unsigned number.
TEST(PrimaryLexing, TimeUnitSeconds) {
  auto tokens = Lex("1s");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitMilliseconds) {
  auto tokens = Lex("1ms");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitMicroseconds) {
  auto tokens = Lex("1us");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitNanoseconds) {
  auto tokens = Lex("1ns");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitPicoseconds) {
  auto tokens = Lex("1ps");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

TEST(PrimaryLexing, TimeUnitFemtoseconds) {
  auto tokens = Lex("1fs");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kTimeLiteral);
}

// §A.8.4 primary_literal ::= number | time_literal | unbased_unsized_literal |
// string_literal — the unbased_unsized_literal alternative produces a
// single token.  (The lexical rule itself is shared with §A.8.7, but A.8.4
// owns the production slot in `primary_literal`.)
TEST(PrimaryLexing, UnbasedUnsizedLiteralZero) {
  auto tokens = Lex("'0");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(PrimaryLexing, UnbasedUnsizedLiteralOne) {
  auto tokens = Lex("'1");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

}  // namespace
