#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

TEST(IdentifierLexing, SimpleIdentSourceLocation) {
  auto [tokens, errors] = LexWithDiag("  foo");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 3u);
}

TEST(IdentifierLexing, CIdentNoDollarChar) {
  auto tokens = Lex("my$func");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my$func");
}

TEST(IdentifierLexing, CIdentValidChars) {
  auto tokens = Lex("my_c_func_123");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my_c_func_123");
}

TEST(IdentifierLexing, MultipleIdentTypes) {
  auto tokens = Lex("foo \\bar $baz");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "bar");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].text, "$baz");
}

TEST(IdentifierLexing, IdentifiersSeparatedByDot) {
  auto tokens = Lex("a.b.c");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].text, "c");
}

TEST(IdentifierLexing, IdentifiersSeparatedByColonColon) {
  auto tokens = Lex("pkg::item");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].text, "item");
}

// --- system_tf_identifier ---

TEST(IdentifierLexing, SystemIdentBasic) {
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(IdentifierLexing, SystemIdentWithDigits) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$clog2");
}

TEST(IdentifierLexing, SystemIdentWithUnderscore) {
  auto tokens = Lex("$read_mem_h");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$read_mem_h");
}

TEST(IdentifierLexing, SystemIdentWithDollar) {
  auto tokens = Lex("$foo$bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$foo$bar");
}

TEST(IdentifierLexing, SystemIdentMaxLength) {
  std::string id = "$" + std::string(1023, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(IdentifierLexing, SystemIdentExceedsMaxLength) {
  std::string id = "$" + std::string(1025, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, BareDollarIsNotSystemIdent) {
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(IdentifierLexing, SystemIdentSourceLocation) {
  auto [tokens, errors] = LexWithDiag("  $finish");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 3u);
}

// §A.9.3 escaped_identifier ::= \ { any_printable_ASCII_character_except_white_space } white_space
// — the body alphabet accepts non-alphanumeric printable characters.  The
// backslash and terminating white_space are not part of the lexeme.
TEST(IdentifierLexing, EscapedIdentifierWithSpecialChars) {
  auto tokens = Lex("\\busy-signal+ ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "busy-signal+");
}

// §A.9.3 escaped_identifier terminator (white_space, per §A.9.4) — newline
// must end the identifier, not extend the body across lines.
TEST(IdentifierLexing, EscapedIdentifierTerminatedByNewline) {
  auto tokens = Lex("\\foo\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
}

// §A.9.3 footnote 55, sentence 2: "A system_tf_identifier shall not be
// escaped."  When `$display` appears after `\`, the lexer must produce an
// escaped_identifier (kEscapedIdentifier) carrying the literal body
// "$display", not a system_tf_identifier (kSystemIdentifier).
TEST(IdentifierLexing, EscapedSystemTfIdentifierIsEscapedNotSystemIdent) {
  auto tokens = Lex("\\$display ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

// §A.9.3 system_tf_identifier ::= $[a-zA-Z0-9_$] { [a-zA-Z0-9_$] } — a digit
// is admissible as the first body character (the alphabet after `$` includes
// 0-9).
TEST(IdentifierLexing, SystemIdentDigitAsFirstBodyChar) {
  auto tokens = Lex("$0 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$0");
}

// §A.9.3 system_tf_identifier — `_` is admissible as the first body character.
TEST(IdentifierLexing, SystemIdentUnderscoreAsFirstBodyChar) {
  auto tokens = Lex("$_my_task ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$_my_task");
}

// §A.9.3 system_tf_identifier — minimum form is `$` + a single body char,
// per `$[a-zA-Z0-9_$] { [a-zA-Z0-9_$] }` (the trailing brace-iterated body is
// zero-or-more).
TEST(IdentifierLexing, SystemIdentSingleCharBody) {
  auto tokens = Lex("$a ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$a");
}

// §A.9.3 system_tf_identifier — uppercase letters are inside the body
// alphabet `[a-zA-Z0-9_$]`.
TEST(IdentifierLexing, SystemIdentUppercaseBody) {
  auto tokens = Lex("$ABC ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$ABC");
}

// §A.9.3 system_tf_identifier — `$` is in the body alphabet, so a trailing
// `$` is part of the identifier (greedy scan stops at first non-body char).
TEST(IdentifierLexing, SystemIdentTrailingDollar) {
  auto tokens = Lex("$test$ ;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$");
}

// §A.9.3 system_tf_identifier — combining the body alphabet (digit, `$`)
// inside the same lexeme.  Cross-checks that the iteration over body chars
// does not stop at an embedded `$` followed by a digit.
TEST(IdentifierLexing, SystemIdentEmbeddedDollarFollowedByDigit) {
  auto tokens = Lex("$test$0plusargs ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$0plusargs");
}

// §A.9.3 system_tf_identifier — multiple system_tf_identifier tokens in the
// same input must be emitted as separate kSystemIdentifier tokens, not glued.
TEST(IdentifierLexing, SystemIdentMultipleInStream) {
  auto tokens = Lex("$display $finish $time");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$finish");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].text, "$time");
}

// §A.9.3 simple_identifier ::= [a-zA-Z_] { [a-zA-Z0-9_$] } — the leading-
// character alphabet `[a-zA-Z_]` includes underscore, so a token beginning
// with `_` must lex as a kIdentifier with the underscore preserved as the
// first character of the lexeme.
TEST(IdentifierLexing, SimpleIdentLeadingUnderscore) {
  auto tokens = Lex("_foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_foo");
}

// §A.9.3 escaped_identifier ::= \ { ... } white_space.  §A.9.4 defines
// white_space ::= space | tab | newline | formfeed | eof — end-of-file is
// itself a white_space form, so `\foo` followed immediately by EOF must lex
// as a kEscapedIdentifier with the body stripped of the leading `\`.
TEST(IdentifierLexing, EscapedIdentifierTerminatedByEof) {
  auto tokens = Lex("\\foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
}

// §A.9.3 system_tf_identifier ::= $[a-zA-Z0-9_$] { [a-zA-Z0-9_$] } — the
// first body-character class includes `$` itself, so a leading `$$` followed
// by further body characters must lex as a single kSystemIdentifier whose
// text begins with `$$`, not as two separate kDollar tokens or as kDollar
// followed by a sub-identifier.
TEST(IdentifierLexing, SystemIdentDollarAsFirstBodyChar) {
  auto tokens = Lex("$$bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$$bar");
}

