#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

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
  EXPECT_TRUE(ReportedError(LexDiagnostics("8' h99"),
                            "the base format character of a based number must "
                            "be written together without white space",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectWhitespaceBetweenApostropheAndBaseAfterSign) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8's h99"),
                            "the base format character of a based number must "
                            "be written together without white space",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, WhitespaceBeforeBaseStillLexesOneIntLiteral) {
  auto tokens = Lex("8' h99");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(IntegerLiteralLexing, ApostropheBeforeCastParenIsItsOwnToken) {
  auto tokens = Lex("4'(x)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostrophe);
}

TEST(IntegerLiteralLexing, IllegalBaseLetterDoesNotFormBasedLiteral) {
  auto r = LexOne("4'y3");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
  EXPECT_EQ(r.token.text, "4");
}

TEST(IntegerLiteralLexing, RejectIllegalBinaryDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'b2"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalOctalDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'o8"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalHexDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'hG"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalLowercaseHexDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'hg"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, IllegalHexDigitLexesOneIntLiteral) {
  auto tokens = Lex("4'hG");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4'hG");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(IntegerLiteralLexing, RejectSignBetweenBaseAndDigits) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'd-6"),
                            "plus or minus operator between the base format "
                            "and the number is illegal syntax",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithX) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'd1x"),
                            "x, z, or ? in decimal literal must be the only "
                            "digit",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithZ) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'd1z"),
                            "x, z, or ? in decimal literal must be the only "
                            "digit",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectDecimalMultiDigitWithQuestion) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'd1?"),
                            "x, z, or ? in decimal literal must be the only "
                            "digit",
                            1, "5.7.1"));
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
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'b_1010"),
                            "underscore cannot be first character of number "
                            "value",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalDecimalDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'da"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectPlusBetweenBaseAndDigits) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'd+6"),
                            "plus or minus operator between the base format "
                            "and the number is illegal syntax",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectMissingValueDigits) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'h;"),
                            "missing value digits after base specifier", 1,
                            "5.7.1"));
}

TEST(IntegerLiteralLexing, MoreThanOneXInADecimalLiteralNames5_7_1) {
  auto diags = LexDiagnostics("2'd1x");
  EXPECT_TRUE(ReportedError(
      diags, "x, z, or ? in decimal literal must be the only digit", 1,
      "5.7.1"));
}

TEST(IntegerLiteralLexing, AcceptDecimalSingleQuestion) {
  auto r = LexWithDiag("4'd?");
  EXPECT_FALSE(r.has_errors);
}

TEST(IntegerLiteralLexing, ColumnAfterNumberAndSpaceIsUnchangedByTheProbe) {
  auto tokens = Lex("3 x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(IntegerLiteralLexing, ColumnAfterSizedLiteralWrittenWithSpaceIsUnchanged) {
  auto tokens = Lex("3 'b1 x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 7u);
}

TEST(IntegerLiteralLexing, ColumnAfterNumberAndTwoSpacesIsUnchanged) {
  auto tokens = Lex("3  x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 4u);
}

TEST(IntegerLiteralLexing, SizelessLiteralRejectsWhitespaceBeforeBaseFormat) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("' h99"),
                            "the base format character of a based number must "
                            "be written together without white space",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing,
     SizelessSignedLiteralRejectsWhitespaceBeforeBaseFormat) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("'s h99"),
                            "the base format character of a based number must "
                            "be written together without white space",
                            1, "5.7.1"));
}

TEST(IntegerLiteralLexing,
     SizelessLiteralWithSpaceBeforeBaseLexesOneIntLiteral) {
  auto tokens = Lex("' h99");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(IntegerLiteralLexing, SizelessCastApostropheBeforeParenIsItsOwnToken) {
  auto tokens = Lex("'(x)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostrophe);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedZeroKeepsItsOwnTokenKind) {
  auto r = LexOne("'0");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(IntegerLiteralLexing, UnbasedUnsizedZeroRejectsWhitespaceAfterApostrophe) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("' 0"), "unexpected character '''",
                            1, "5.2"));
}

TEST(IntegerLiteralLexing, SizelessLiteralAllowsWhitespaceBeforeDigits) {
  EXPECT_TRUE(LexDiagnostics("'h 837FF").empty());
}

TEST(IntegerLiteralLexing, SizelessLiteralSpansTheDigitsAfterTheWhitespace) {
  auto tokens = Lex("'h 837FF");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(IntegerLiteralLexing, TabBeforeTheApostropheIsAllowedAndAfterItIsNot) {
  auto tokens = Lex("8\t'h1");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "8\t'h1");
  EXPECT_TRUE(LexDiagnostics("8\t'h1").empty());

  EXPECT_TRUE(ReportedError(LexDiagnostics("8'\th1"),
                            "must be written together without white space", 1,
                            "5.7.1"));
}

TEST(IntegerLiteralLexing, ApostropheEndingTheTextIsAnUnexpectedCharacter) {
  EXPECT_TRUE(
      ReportedError(LexDiagnostics("x = '"), "unexpected character", 1, "5.2"));
}

TEST(IntegerLiteralLexing, NewlineBetweenBaseAndDigits) {
  auto r = LexWithDiag("8'h\n  FF");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.tokens.size(), 2u);
  EXPECT_EQ(r.tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, FormfeedBetweenBaseAndDigits) {
  auto r = LexWithDiag("8'h\fFF");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.tokens.size(), 2u);
  EXPECT_EQ(r.tokens[0].kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, UnderscoreFirstInABasedValueIsReported) {
  for (const char* src :
       {"8'h_F", "'h_F", "8'h _F", "8'd_5", "8'o_7", "4'sb_1", "'SH_a"}) {
    EXPECT_TRUE(ReportedError(LexDiagnostics(src),
                              "underscore cannot be first character of number "
                              "value",
                              1, "5.7.1"))
        << src;
  }
  for (const char* src :
       {"8'hF", "'hF", "8'h F", "8'd5", "8'o7", "4'sb1", "'SHa"}) {
    EXPECT_TRUE(LexDiagnostics(src).empty()) << src;
  }
}

TEST(IntegerLiteralLexing, TrailingDoubledAndSizeUnderscoresLexAsOneToken) {
  for (const char* src : {"12_", "8'hF_", "4'b10_", "1__2", "8'b1__0",
                          "'h1___F", "1_6'h12", "1__0_.2__5_", "2_5e0__1_"}) {
    auto r = LexWithDiag(src);
    EXPECT_FALSE(r.has_errors) << src;
    ASSERT_EQ(r.tokens.size(), 2u) << src;
    EXPECT_EQ(r.tokens[0].text, src) << src;
  }
}

TEST(IntegerLiteralLexing,
     WhiteSpaceAfterAnUnbasedUnsizedApostropheIsReported) {
  for (const char* src :
       {"' x", "' X", "' z", "' Z", "'\t1", "'\n1", "'\f0", "'\tx"}) {
    EXPECT_TRUE(ReportedError(LexDiagnostics(src), "unexpected character '''",
                              1, "5.2"))
        << src;
  }
}

TEST(IntegerLiteralLexing, EachUnbasedUnsizedFormIsOneToken) {
  for (const char* src : {"'0", "'1", "'x", "'X", "'z", "'Z"}) {
    auto r = LexWithDiag(src);
    EXPECT_FALSE(r.has_errors) << src;
    ASSERT_EQ(r.tokens.size(), 2u) << src;
    EXPECT_EQ(r.tokens[0].kind, TokenKind::kUnbasedUnsizedLiteral) << src;
    EXPECT_EQ(r.tokens[0].text, src) << src;
  }
}

}  // namespace
