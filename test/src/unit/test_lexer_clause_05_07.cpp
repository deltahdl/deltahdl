#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(NumberLexing, WhitespaceAfterApostropheNotUnbasedUnsized) {
  auto tokens = Lex("' 1 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_NE(tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(NumberLexing, WhitespaceBetweenApostropheAndBase) {
  auto tokens = Lex("8' hFF ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8");
}

TEST(NumberLexing, IllegalBinaryDigit) {
  auto [tokens, errors] = LexWithDiag("4'b3 ");
  EXPECT_TRUE(errors);
}

TEST(NumberLexing, IllegalOctalDigit) {
  auto [tokens, errors] = LexWithDiag("8'o9 ");
  EXPECT_TRUE(errors);
}

TEST(NumberLexing, UnderscoreFirstInHexValue) {
  auto [tokens, errors] = LexWithDiag("8'h_FF ");
  EXPECT_TRUE(errors);
}

TEST(NumberLexing, UnderscoreFirstInBinaryValue) {
  auto [tokens, errors] = LexWithDiag("4'b_1010 ");
  EXPECT_TRUE(errors);
}

}  // namespace
