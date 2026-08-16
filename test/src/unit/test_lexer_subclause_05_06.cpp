#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, SimpleIdentLetters) {
  auto r = LexOne("abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "abc");
}

TEST(LexicalConventionLexing, SimpleIdentDigits) {
  auto r = LexOne("val42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "val42");
}

TEST(LexicalConventionLexing, SimpleIdentUnderscore) {
  auto r = LexOne("_bus3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "_bus3");
}

TEST(LexicalConventionLexing, SimpleIdentDollar) {
  auto r = LexOne("n$657 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "n$657");
}

TEST(LexicalConventionLexing, SimpleIdentMixed) {
  auto r = LexOne("abc_123$xyz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "abc_123$xyz");
}

// §5.6: "The first character of a simple identifier shall not be a digit or
// $". The lexer does not report `42abc`, it splits it: Lexer::Next() sends a
// leading digit to Lexer::LexNumber(), which stops at `a` and yields the
// integer literal `42`, and the identifier scan then takes `abc`. This fails
// if the digit run is folded into one identifier token, or if the text of
// either token moves the boundary between them.
TEST(LexicalConventionLexing, DigitStartIsNumber) {
  auto tokens = Lex("42abc ");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "abc");
}

// §5.6 bars the leading $ from a simple identifier, and §5.6.3 rules that "A
// name following the $ is interpreted as a system task or a system function".
// This fails if `$abc` comes back as anything but the system identifier, or if
// its text drops the `$` that decides the interpretation.
TEST(LexicalConventionLexing, DollarStartIsNotIdentifier) {
  auto r = LexOne("$abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$abc");
}

// §5.6: "A keyword (see 5.6.2) may not be used as a user-defined identifier."
// Lexer::LexIdentifier() scans the word and hands it to LookupKeyword(), so
// `module` comes back under its own kind rather than as an identifier. This
// fails if the keyword table stops covering `module` for the version in force.
TEST(LexicalConventionLexing, KeywordIsNotIdentifier) {
  auto r = LexOne("module ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
  EXPECT_EQ(r.token.text, "module");
}

TEST(LexicalConventionLexing, CaseSensitive) {
  auto tokens = Lex("ABC abc Abc");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "ABC");
  EXPECT_EQ(tokens[1].text, "abc");
  EXPECT_EQ(tokens[2].text, "Abc");
}

TEST(LexicalConventionLexing, MaxLength1024Ok) {
  std::string id(1024, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(LexicalConventionLexing, MaxLength1025Error) {
  std::string id(1025, 'a');
  auto diags = LexDiagnostics(id);
  EXPECT_TRUE(ReportedError(
      diags, "identifier exceeds maximum length of 1024 characters", 1, "5.6"));
}

TEST(LexicalConventionLexing, EscapedMaxLength1025Error) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  auto diags = LexDiagnostics(id);
  EXPECT_TRUE(ReportedError(
      diags, "identifier exceeds maximum length of 1024 characters", 1, "5.6"));
}

TEST(LexicalConventionLexing, EscapedMaxLength1024Ok) {
  std::string id = "\\" + std::string(1024, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

// The limit reads like an internal one and is not. §5.6 states:
// "Implementations may set a limit on the maximum length of identifiers, but
// the limit shall be at least 1024 characters. If an identifier exceeds the
// implementation-specific length limit, an error shall be reported." The
// standard requires the report, so the record names 5.6 rather than leaving the
// number to look like a fact about this run.
TEST(LexicalConventionLexing, OverLimitIdentifierNames5_6) {
  auto diags = LexDiagnostics(std::string(1025, 'a'));
  EXPECT_TRUE(ReportedError(
      diags, "identifier exceeds maximum length of 1024 characters", 1, "5.6"));
}

TEST(LexicalConventionLexing, IdentifierFollowedByOperator) {
  auto tokens = Lex("abc+def");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "def");
}

}  // namespace
