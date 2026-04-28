#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, BasicEscapedIdentifier) {
  auto r = LexOne("\\cpu3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "cpu3");
}

TEST(LexicalConventionLexing, TerminatedBySpace) {
  auto tokens = Lex("\\esc_id next");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "next");
}

TEST(LexicalConventionLexing, SpecialCharsInEscaped) {
  auto r = LexOne("\\***error-condition*** ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "***error-condition***");
}

TEST(LexicalConventionLexing, ForwardSlash) {
  auto r = LexOne("\\net1/\\net2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "net1/\\net2");
}

TEST(LexicalConventionLexing, Braces) {
  auto r = LexOne("\\{a,b} ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "{a,b}");
}

TEST(LexicalConventionLexing, PlusSign) {
  auto r = LexOne("\\busa+index ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "busa+index");
}

TEST(LexicalConventionLexing, EscapedKeywordIsIdentifier) {
  auto r = LexOne("\\module ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kKwModule);
}

TEST(LexicalConventionLexing, MaxLengthOk) {
  std::string id = "\\" + std::string(1023, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

TEST(LexicalConventionLexing, MultipleEscapedInSequence) {
  auto tokens = Lex("\\abc \\def \\ghi ");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[2].text, "ghi");
}

TEST(LexicalConventionLexing, DashClock) {
  auto r = LexOne("\\-clock ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "-clock");
}

TEST(LexicalConventionLexing, ParenthesesInEscaped) {
  auto r = LexOne("\\a*(b+c) ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "a*(b+c)");
}

TEST(LexicalConventionLexing, MinPrintableAsciiChar) {
  auto r = LexOne("\\! ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "!");
}

TEST(LexicalConventionLexing, MaxPrintableAsciiChar) {
  auto r = LexOne("\\~ ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "~");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByNewline) {
  auto tokens = Lex("\\abc\ndef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByTab) {
  auto tokens = Lex("\\abc\tdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, EscapedIdentifierAtEof) {
  auto tokens = Lex("\\abc");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByFormfeed) {
  auto tokens = Lex("\\abc\fdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

TEST(LexicalConventionLexing, EscapedAndSimpleIdentLexToSameText) {
  auto escaped = LexOne("\\cpu3 ");
  auto simple = LexOne("cpu3");
  EXPECT_EQ(escaped.token.text, simple.token.text);
  EXPECT_EQ(escaped.token.text, "cpu3");
}

// §5.6.1: white space terminator covers carriage return.
TEST(LexicalConventionLexing, EscapedIdentifierTerminatedByCarriageReturn) {
  auto tokens = Lex("\\abc\rdef");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
}

// §5.6.1: escaped body may begin with a digit (simple identifiers cannot).
TEST(LexicalConventionLexing, EscapedIdentifierStartingWithDigit) {
  auto r = LexOne("\\1234 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "1234");
}

// §5.6.1: lexer preserves case of body characters verbatim.
TEST(LexicalConventionLexing, EscapedIdentifierPreservesCase) {
  auto r = LexOne("\\AbCdEf ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "AbCdEf");
}

// §5.6.1: body restricted to printable ASCII (33-126). Non-whitespace
// control characters below 33 are rejected.
TEST(LexicalConventionLexing, EscapedIdentifierRejectsControlCharBelow33) {
  std::string src = "\\ab";
  src += '\x01';
  src += "cd ";
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_TRUE(errors);
}

// §5.6.1: DEL (0x7F = 127) is outside the printable ASCII range.
TEST(LexicalConventionLexing, EscapedIdentifierRejectsDel) {
  std::string src = "\\ab";
  src += '\x7F';
  src += "cd ";
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_TRUE(errors);
}

// §5.6.1: Bytes with the high bit set are outside the printable ASCII range.
TEST(LexicalConventionLexing, EscapedIdentifierRejectsHighByte) {
  std::string src = "\\ab";
  src += static_cast<char>(0x80);
  src += "cd ";
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_TRUE(errors);
}

// §5.6.1: an escaped identifier whose terminator immediately follows the
// leading backslash has an empty body (zero characters between \ and the
// terminating whitespace).
TEST(LexicalConventionLexing, EscapedIdentifierEmptyBodyAtSpace) {
  auto [tokens, errors] = LexWithDiag("\\ foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_TRUE(tokens[0].text.empty());
}

// §5.6.1: leading backslash and terminating whitespace are not part of the
// identifier, even when the escaped form is interleaved with simple
// identifiers in a token stream.
TEST(LexicalConventionLexing, SimpleAndEscapedInStream) {
  auto tokens = Lex("abc \\def ghi");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "def");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ghi");
}

// §5.6.1: a `+` sign embedded in the body is part of the escaped identifier;
// inserting whitespace before the `+` terminates the escaped identifier and
// the `+` becomes its own operator token.
TEST(LexicalConventionLexing, EscapedIdentifierWhitespaceIsSignificant) {
  auto without_ws = Lex("\\foo+bar ");
  ASSERT_GE(without_ws.size(), 2u);
  EXPECT_EQ(without_ws[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(without_ws[0].text, "foo+bar");

  auto with_ws = Lex("\\foo +bar ");
  ASSERT_GE(with_ws.size(), 4u);
  EXPECT_EQ(with_ws[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(with_ws[0].text, "foo");
  EXPECT_EQ(with_ws[1].kind, TokenKind::kPlus);
  EXPECT_EQ(with_ws[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(with_ws[2].text, "bar");
}

// §5.6.1: a leading backslash starts an escaped identifier whose body may
// include `$` (printable ASCII 0x24). The `\` dispatch precedes the
// system-identifier dispatch, so `\$display` is an escaped identifier, not a
// system identifier.
TEST(LexicalConventionLexing, EscapedDollarIsNotSystemId) {
  auto r = LexOne("\\$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

// §5.6.1: rule (1) "end with white space" combined with rule (2) "any printable
// ASCII except white space" implies the body absorbs every non-whitespace
// printable byte — including the bytes that would normally begin a string
// literal ("), a line comment (//), a block comment (/*), or a number-base
// apostrophe ('). The lexer must not dispatch to string or comment handling
// from inside an escaped identifier body; it must continue scanning until the
// first whitespace.
TEST(LexicalConventionLexing, EscapedIdentifierBodyAbsorbsStructuralDelimiters) {
  auto r = LexOne("\\foo\"bar/*baz//qux'end ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "foo\"bar/*baz//qux'end");
}

// §5.6.1: rule (1) "shall start with the backslash character (\) and end with
// white space" combined with §5.3's inclusion of end-of-file in the white
// space category implies that a bare backslash followed only by EOF is a
// well-formed escaped identifier with an empty body. Production code must
// not over-read past the source buffer.
TEST(LexicalConventionLexing, EscapedIdentifierBareBackslashAtEof) {
  auto [tokens, errors] = LexWithDiag("\\");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_TRUE(tokens[0].text.empty());
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

}  // namespace
