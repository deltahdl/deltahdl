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

TEST(IntegerLiteralLexing, IllegalBaseLetterDoesNotFormBasedLiteral) {
  // §5.7.1: the only legal base letters are d/D, h/H, o/O, b/B. A letter
  // outside that set (here 'y') must not be recognized as a base format, so
  // the leading size digits stay a bare integer token rather than being
  // absorbed into a single based-literal token spanning "4'y3".
  auto r = LexOne("4'y3");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4");
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

// §5.7.1: the value digits must be legal for the declared base. 'a' is a hex
// digit but not a decimal digit, so a decimal-based literal must reject it.
// This is the decimal counterpart of the binary/octal/hex illegal-digit cases.
TEST(IntegerLiteralLexing, RejectIllegalDecimalDigit) {
  auto r = LexWithDiag("4'da");
  EXPECT_TRUE(r.has_errors);
}

// §5.7.1: a plus or minus sign between the base format and the value digits is
// illegal. The minus form is covered elsewhere; this pins the plus form.
TEST(IntegerLiteralLexing, RejectPlusBetweenBaseAndDigits) {
  auto r = LexWithDiag("8'd+6");
  EXPECT_TRUE(r.has_errors);
}

// §5.7.1: the value is a required token of a based literal — a base format with
// no following value digits is malformed.
TEST(IntegerLiteralLexing, RejectMissingValueDigits) {
  auto r = LexWithDiag("8'h;");
  EXPECT_TRUE(r.has_errors);
}

// §5.7.1: '?' is the SystemVerilog alternative for the z digit, so it is one of
// the x/z/? digits a decimal literal may carry as its single lone digit.
TEST(IntegerLiteralLexing, AcceptDecimalSingleQuestion) {
  auto r = LexWithDiag("4'd?");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
