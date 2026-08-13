#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"

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
  // §5.7.1 states "The apostrophe character and the base format character shall
  // not be separated by any white space", and no site in src/lexer/lexer.cpp
  // reports that sentence. ApostropheStartsBaseSpecifier reads past the
  // apostrophe, finds a space where a base letter must stand and returns false,
  // so Lexer::LexNumber ends the number at `8` and the apostrophe reaches
  // Lexer::LexApostrophe, which falls through to Lexer::LexOperator. The report
  // the source actually gets is that function's §5.2 unexpected-character one.
  EXPECT_TRUE(ReportedError(LexDiagnostics("8' h99"),
                            "unexpected character '''", 1, "5.2"));
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
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'b2"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalOctalDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'o8"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectIllegalHexDigit) {
  // The report is the missing-value one rather than the illegal-digit one the
  // name leads a reader to expect. The value-digit loop in
  // Lexer::LexBasedNumber accepts only std::isxdigit characters, `_`, x, X, z,
  // Z and ?, so `G` ends the run before it starts and Lexer::ValidateBaseDigits
  // is handed an empty span. That loop and the 'h'/'H' case of
  // Lexer::ValidateBaseDigits accept exactly the same characters, so no source
  // reaches that case with a digit it rejects.
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'hG"),
                            "missing value digits after base specifier", 1,
                            "5.7.1"));
}

TEST(IntegerLiteralLexing, RejectSignBetweenBaseAndDigits) {
  // §5.7.1 rules that "A plus or minus operator between the base format and the
  // number is an illegal syntax", and the report names the neighbouring
  // sentence of the same subclause instead: `-` is not a character the
  // value-digit loop in Lexer::LexBasedNumber accepts, so the literal is
  // rejected for carrying no value digits at all.
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'd-6"),
                            "missing value digits after base specifier", 1,
                            "5.7.1"));
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

// §5.7.1: the value digits must be legal for the declared base. 'a' is a hex
// digit but not a decimal digit, so a decimal-based literal must reject it.
// This is the decimal counterpart of the binary/octal/hex illegal-digit cases.
TEST(IntegerLiteralLexing, RejectIllegalDecimalDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'da"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

// §5.7.1: a plus or minus sign between the base format and the value digits is
// illegal. The minus form is covered elsewhere; this pins the plus form.
TEST(IntegerLiteralLexing, RejectPlusBetweenBaseAndDigits) {
  // As with the minus form above, `+` ends the value-digit run in
  // Lexer::LexBasedNumber before it begins, so the report names the missing
  // value digits rather than the sign.
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'd+6"),
                            "missing value digits after base specifier", 1,
                            "5.7.1"));
}

// §5.7.1: the value is a required token of a based literal — a base format with
// no following value digits is malformed.
TEST(IntegerLiteralLexing, RejectMissingValueDigits) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'h;"),
                            "missing value digits after base specifier", 1,
                            "5.7.1"));
}

// §5.7.1 states the rule in these words: "In a decimal literal constant, the
// unsigned number token shall not contain any x, z, or ? digits, unless there
// is exactly one digit in the token". The rejection records that subclause, so
// an assertion can claim this rule was enforced rather than the one about
// digits legal for the base, which the same literal can also breach.
TEST(IntegerLiteralLexing, MoreThanOneXInADecimalLiteralNames5_7_1) {
  auto diags = LexDiagnostics("2'd1x");
  ASSERT_EQ(diags.size(), 1u);
  EXPECT_EQ(diags.front().subclause, "5.7.1");
}

// §5.7.1: '?' is the SystemVerilog alternative for the z digit, so it is one of
// the x/z/? digits a decimal literal may carry as its single lone digit.
TEST(IntegerLiteralLexing, AcceptDecimalSingleQuestion) {
  auto r = LexWithDiag("4'd?");
  EXPECT_FALSE(r.has_errors);
}

// §5.7.1 permits white space between the size and the apostrophe, which
// Example 2 writes as `5 'D 3`, so lexing a number has to read past white space
// to learn whether a base specifier follows it. The three cases below assert
// what that lookahead owes the rest of the line: a token is located at the
// column it is written in whichever way the lookahead turns out. Every
// diagnostic reported at a token reads its column, and DiagEngine::Emit draws
// a caret there.

// The lookahead read one space and found no apostrophe, so `3` and `x` are two
// tokens and the space belongs to neither.
TEST(IntegerLiteralLexing, ColumnAfterNumberAndSpaceIsUnchangedByTheProbe) {
  auto tokens = Lex("3 x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

// The other way the lookahead can turn out: the apostrophe is there, the white
// space belongs to the number, and the column has to come out right along that
// path too.
TEST(IntegerLiteralLexing, ColumnAfterSizedLiteralWrittenWithSpaceIsUnchanged) {
  auto tokens = Lex("3 'b1 x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 7u);
}

// Two spaces rather than one, because one space makes an off-by-one column
// indistinguishable from a column reset by a constant.
TEST(IntegerLiteralLexing, ColumnAfterNumberAndTwoSpacesIsUnchanged) {
  auto tokens = Lex("3  x");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[1].loc.column, 4u);
}

}  // namespace
