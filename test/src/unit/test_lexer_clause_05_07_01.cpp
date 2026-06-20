#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(IntegerLiteralLexing, WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, SpaceBreaksNumberIntoTwo) {
  auto tokens = Lex("12 34");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, RejectWhitespaceBetweenApostropheAndBase) {
  auto r = LexWithDiag("8' h99");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectIllegalBinaryDigit) {
  auto r = LexWithDiag("4'b2");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectIllegalOctalDigit) {
  auto r = LexWithDiag("4'o8");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectIllegalHexDigit) {
  auto r = LexWithDiag("4'hG");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectSignBetweenBaseAndDigits) {
  auto r = LexWithDiag("8'd-6");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithX) {
  auto r = LexWithDiag("4'd1x");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithZ) {
  auto r = LexWithDiag("4'd1z");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithQuestion) {
  auto r = LexWithDiag("4'd1?");
  EXPECT_TRUE(r.has_errors);
}

TEST(IntegerLiteralLexing, AcceptDecimalSingleX) {
  auto r = LexWithDiag("4'dx");
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralLexing, AcceptDecimalSingleZ) {
  auto r = LexWithDiag("4'dz");
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralLexing, RejectLeadingUnderscoreInValue) {
  auto r = LexWithDiag("4'b_1010");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
