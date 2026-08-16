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
  // not be separated by any white space". `8' h99` writes a space between the
  // apostrophe and the `h`, and the report stands at the start of the number
  // token, which is line 1 here.
  EXPECT_TRUE(ReportedError(LexDiagnostics("8' h99"),
                            "white space shall not separate the apostrophe "
                            "from the base format character",
                            1, "5.7.1"));
}

// §5.7.1: the base format character is the letter, so the `s` marker written
// tight against the apostrophe does not satisfy the sentence. `8's h99` still
// separates the apostrophe from the `h` by white space and is rejected under
// the same rule as `8' h99`.
TEST(IntegerLiteralLexing, RejectWhitespaceBetweenApostropheAndBaseAfterSign) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("8's h99"),
                            "white space shall not separate the apostrophe "
                            "from the base format character",
                            1, "5.7.1"));
}

// §5.7.1 leaves `8' h99` a based literal that breaks one of its rules, so the
// lexer reports the white space and then lexes what was written: one
// kIntLiteral token followed by the end of file, rather than the number,
// operator and identifier the source splits into when the apostrophe is left
// to Lexer::LexApostrophe.
TEST(IntegerLiteralLexing, WhitespaceBeforeBaseStillLexesOneIntLiteral) {
  auto tokens = Lex("8' h99");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

// §6.24.1 writes a cast as `size'(expr)`, where the apostrophe is a token of
// its own and no base specifier follows it. Reading white space past the
// apostrophe to enforce §5.7.1 must not take this form with it: `4` stays an
// integer literal and the apostrophe stays a kApostrophe token.
TEST(IntegerLiteralLexing, ApostropheBeforeCastParenIsItsOwnToken) {
  auto tokens = Lex("4'(x)");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kApostrophe);
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

// §5.7.1 rules that "The third token, an unsigned number, shall consist of
// digits that are legal for the specified base format", and `G` is legal for no
// base. This case is what makes the 'h'/'H' arm of Lexer::ValidateBaseDigits
// reachable: it goes red if the value run in Lexer::LexBasedNumber stops at `G`
// instead of collecting it, because the literal is then reported as one with no
// value at all.
TEST(IntegerLiteralLexing, RejectIllegalHexDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'hG"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

// §5.7.1 rules that "The hexadecimal digits a to f shall be case insensitive",
// so `g` is illegal in the case `G` is illegal in. The two cases are decided by
// one std::isxdigit call, and this one goes red for a rejection written to read
// uppercase offenders alone.
TEST(IntegerLiteralLexing, RejectIllegalLowercaseHexDigit) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("4'hg"),
                            "illegal digit for specified base", 1, "5.7.1"));
}

// §5.7.1 gives a based literal three tokens, the third of which is the value,
// so an illegal digit written in the value belongs to the literal rather than
// starting an identifier after it. `4'hG` is therefore one kIntLiteral spanning
// the whole source, and this fails if the value run stops at `G` and leaves it
// to Lexer::LexIdentifier.
TEST(IntegerLiteralLexing, IllegalHexDigitLexesOneIntLiteral) {
  auto tokens = Lex("4'hG");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "4'hG");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

// §5.7.1 rules that "A plus or minus operator between the base format and the
// number is an illegal syntax", and its Example 3 writes `8 'd -6` as illegal
// syntax. This fails when the sign is reported as the neighbouring sentence of
// the same subclause, which is what a literal carrying no value token at all
// breaches.
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
  EXPECT_TRUE(ReportedError(LexDiagnostics("8'd+6"),
                            "plus or minus operator between the base format "
                            "and the number is illegal syntax",
                            1, "5.7.1"));
}

// §5.7.1: the value is a required token of a based literal — a base format with
// no following value digits is malformed. `8'h;` is the one source in this file
// that really carries no value token, so this is the case that keeps the report
// alive: a lexer answering every breach of the value token with the sign or
// illegal-digit message satisfies the cases above and fails only here.
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
  EXPECT_TRUE(ReportedError(
      diags, "x, z, or ? in decimal literal must be the only digit", 1,
      "5.7.1"));
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

// §5.7.1 composes a based literal of "up to three tokens—an optional size
// constant, an apostrophe character (') followed by a base format character,
// and the digits representing the value of the number", so a literal written
// with no size constant is still a based literal. The sentence "The apostrophe
// character and the base format character shall not be separated by any white
// space" therefore governs `' h99` exactly as it governs `8' h99`.
TEST(IntegerLiteralLexing, SizelessLiteralRejectsWhitespaceBeforeBaseFormat) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("' h99"),
                            "white space shall not separate the apostrophe "
                            "from the base format character",
                            1, "5.7.1"));
}

// §5.7.1: the base format character is the letter, not the optional s/S signed
// marker, so writing the marker tight against the apostrophe does not satisfy
// the sentence. `'s h99` separates the apostrophe from the `h` by white space
// and is rejected under the same rule as `' h99`.
TEST(IntegerLiteralLexing,
     SizelessSignedLiteralRejectsWhitespaceBeforeBaseFormat) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("'s h99"),
                            "white space shall not separate the apostrophe "
                            "from the base format character",
                            1, "5.7.1"));
}

// §5.7.1 leaves `' h99` a based literal that breaks one of its rules, so the
// lexer reports the white space and then lexes what was written: one
// kIntLiteral token followed by the end of file, rather than the apostrophe
// operator and identifier the source splits into when the apostrophe is left
// to Lexer::LexOperator.
TEST(IntegerLiteralLexing,
     SizelessLiteralWithSpaceBeforeBaseLexesOneIntLiteral) {
  auto tokens = Lex("' h99");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

// A.8.4 writes the cast production as `casting_type ' ( expression )`, where
// the apostrophe is a token of its own and no base format character follows
// it. Reading white space past the apostrophe to enforce §5.7.1 must not take
// this form with it, and the size constant §5.7.1 makes optional is absent
// here too, so the apostrophe stays a kApostrophe token with nothing before it.
TEST(IntegerLiteralLexing, SizelessCastApostropheBeforeParenIsItsOwnToken) {
  auto tokens = Lex("'(x)");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kApostrophe);
}

// §5.7.1 writes "An unsized unsigned single-bit value can be specified by
// preceding the single-bit value with an apostrophe ('), but without the base
// specifier", giving `'0`, `'1`, `'X`, `'x`, `'Z` and `'z`. They carry no base
// format character at all, so the sentence "The apostrophe character and the
// base format character shall not be separated by any white space" says nothing
// about them, and routing `' h99` to Lexer::LexBasedNumber must leave `'0`
// lexing as one kUnbasedUnsizedLiteral token.
TEST(IntegerLiteralLexing, UnbasedUnsizedZeroKeepsItsOwnTokenKind) {
  auto r = LexOne("'0");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

// A.8.7 writes `unbased_unsigned_literal ::= '0 | '1 | 'x | 'X | 'z | 'Z`, and
// each of those six alternatives is a single terminal of the grammar. No white
// space stands inside a terminal, so `' 0` is not an unbased unsigned literal
// and the apostrophe reaches Lexer::LexOperator, which reports it. Widening the
// lookahead in Lexer::LexApostrophe so that `int ' (x)` lexes as the cast of
// A.8.4 must leave this rejection standing.
TEST(IntegerLiteralLexing, UnbasedUnsizedZeroRejectsWhitespaceAfterApostrophe) {
  EXPECT_TRUE(ReportedError(LexDiagnostics("' 0"), "unexpected character '''",
                            1, "5.2"));
}

// §5.7.1 writes "The unsigned number token shall immediately follow the base
// format, optionally preceded by white space", and its Example 1 gives the
// size-less `'h 837FF` as a hexadecimal number. That white space stands after
// the base format rather than before it, so the same route that reports the
// separation §5.7.1 forbids must take this literal without a word: one
// kIntLiteral spanning it, and nothing reported.
TEST(IntegerLiteralLexing, SizelessLiteralAllowsWhitespaceBeforeDigits) {
  EXPECT_TRUE(LexDiagnostics("'h 837FF").empty());
}

// The same literal of §5.7.1's Example 1, read for what it lexes to. The white
// space before the digits is inside the literal rather than ending it, so the
// digits belong to the number and not to an identifier after it.
TEST(IntegerLiteralLexing, SizelessLiteralSpansTheDigitsAfterTheWhitespace) {
  auto tokens = Lex("'h 837FF");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
