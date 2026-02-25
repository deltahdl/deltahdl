// §A.9.3 Identifiers — lexer-level tests

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

static std::vector<Token> Lex(const std::string &src) {
  static SourceManager mgr;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  return lexer.LexAll();
}

struct LexResult {
  std::vector<Token> tokens;
  bool has_errors;
};

static LexResult LexWithDiag(const std::string &src) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto tokens = lexer.LexAll();
  return {tokens, diag.HasErrors()};
}

// ===========================================================================
// §A.9.3 / §5.6: identifier ::= simple_identifier | escaped_identifier
// ===========================================================================

// ---------------------------------------------------------------------------
// simple_identifier54 ::= [ a-zA-Z_ ] { [ a-zA-Z0-9_$ ] }
// Footnote 54: shall start with alpha or underscore, at least one char, no spaces
// ---------------------------------------------------------------------------

TEST(LexerA93, SimpleIdentSingleChar) {
  // §A.9.3: Minimum valid simple_identifier: one alpha character.
  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerA93, SimpleIdentSingleUnderscore) {
  // §A.9.3: Underscore alone is a valid simple_identifier.
  auto tokens = Lex("_");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_");
}

TEST(LexerA93, SimpleIdentAllAlpha) {
  auto tokens = Lex("myIdentifier");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "myIdentifier");
}

TEST(LexerA93, SimpleIdentAlphaNumUnderscore) {
  // §A.9.3: simple_identifier may contain a-zA-Z0-9_ after the first char.
  auto tokens = Lex("data_bus_32bit");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "data_bus_32bit");
}

TEST(LexerA93, SimpleIdentWithDollar) {
  // §A.9.3: simple_identifier allows $ in subsequent characters.
  auto tokens = Lex("my$var");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my$var");
}

TEST(LexerA93, SimpleIdentStartUppercase) {
  auto tokens = Lex("Module_A");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "Module_A");
}

TEST(LexerA93, SimpleIdentLeadingUnderscores) {
  auto tokens = Lex("__private_var");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "__private_var");
}

TEST(LexerA93, SimpleIdentMaxLength) {
  // §5.6 / Footnote 54: Implementation limit shall be at least 1024 chars.
  std::string id(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(LexerA93, SimpleIdentExceedsMaxLength) {
  // §5.6: Error when identifier exceeds 1024 chars.
  std::string id(1025, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexerA93, SimpleIdentCaseSensitive) {
  // §5.6: Identifiers are case-sensitive.
  auto tokens = Lex("foo FOO Foo");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "FOO");
  EXPECT_EQ(tokens[2].text, "Foo");
}

TEST(LexerA93, SimpleIdentKeywordDisambiguation) {
  // §A.9.3: Keywords like 'module' are not simple_identifiers.
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
}

TEST(LexerA93, SimpleIdentNotKeyword) {
  // §A.9.3: 'modules' is not a keyword — it is an identifier.
  auto tokens = Lex("modules");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "modules");
}

TEST(LexerA93, SimpleIdentSourceLocation) {
  // §A.9.3: Source location of identifier.
  auto [tokens, errors] = LexWithDiag("  foo");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 3u);
}

// ---------------------------------------------------------------------------
// escaped_identifier ::= \ { any_printable_ASCII_character_except_white_space } white_space
// ---------------------------------------------------------------------------

TEST(LexerA93, EscapedIdentBasic) {
  // §A.9.3: Escaped identifier starts with backslash, ends at whitespace.
  auto tokens = Lex("\\my_id ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\my_id");
}

TEST(LexerA93, EscapedIdentWithKeyword) {
  // §5.6.1: Escaped identifiers allow using keywords as names.
  auto tokens = Lex("\\module ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\module");
}

TEST(LexerA93, EscapedIdentWithSpecialChars) {
  // §A.9.3: Any printable ASCII except whitespace is allowed.
  auto tokens = Lex("\\a+b*c/d ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\a+b*c/d");
}

TEST(LexerA93, EscapedIdentTerminatedByNewline) {
  // §A.9.3: Newline is whitespace — terminates escaped identifier.
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA93, EscapedIdentTerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA93, EscapedIdentWithBraces) {
  auto tokens = Lex("\\{net} ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\{net}");
}

TEST(LexerA93, EscapedIdentWithBrackets) {
  auto tokens = Lex("\\bus[0] ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\bus[0]");
}

TEST(LexerA93, EscapedIdentMaxLength) {
  std::string id = "\\" + std::string(1023, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

TEST(LexerA93, EscapedIdentExceedsMaxLength) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexerA93, EscapedIdentFollowedByToken) {
  // Escaped identifier terminated by space, followed by another token.
  auto tokens = Lex("\\my_id ; \\next_id ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\my_id");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[2].text, "\\next_id");
}

// ---------------------------------------------------------------------------
// c_identifier54 ::= [ a-zA-Z_ ] { [ a-zA-Z0-9_ ] }
// Footnote 54: Same start rules as simple_identifier but NO $ character.
// ---------------------------------------------------------------------------

TEST(LexerA93, CIdentNoDollarChar) {
  // §A.9.3: c_identifier does not allow $. The lexer produces a normal
  // identifier token; the parser validates the c_identifier constraint in
  // DPI import/export context (§35). Lexing "my$func" gives one token.
  auto tokens = Lex("my$func");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my$func");
}

TEST(LexerA93, CIdentValidChars) {
  // §A.9.3: Pure c_identifier with only [a-zA-Z0-9_] characters.
  auto tokens = Lex("my_c_func_123");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my_c_func_123");
}

// ---------------------------------------------------------------------------
// system_tf_identifier55 ::= $[ a-zA-Z0-9_$ ]{ [ a-zA-Z0-9_$ ] }
// Footnote 55: $ not followed by whitespace, not escaped.
// ---------------------------------------------------------------------------

TEST(LexerA93, SystemIdBasic) {
  // §A.9.3: System task/function identifier starts with $.
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(LexerA93, SystemIdWithUnderscore) {
  auto tokens = Lex("$read_mem_h");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$read_mem_h");
}

TEST(LexerA93, SystemIdWithDigits) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$clog2");
}

TEST(LexerA93, SystemIdEmbeddedDollar) {
  // §A.9.3: $ may appear within system_tf_identifier name body.
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(LexerA93, SystemIdMaxLength) {
  std::string id = "$" + std::string(1023, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(LexerA93, SystemIdExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexerA93, DollarAloneIsNotSystemId) {
  // §A.9.3 / Footnote 55: Bare $ followed by whitespace is kDollar, not system id.
  auto tokens = Lex("$ ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(LexerA93, DollarFollowedByDigit) {
  // §A.9.3: $ followed by digit — bare $ token then integer literal.
  auto tokens = Lex("$0");
  ASSERT_GE(tokens.size(), 2u);
  // $ not followed by alpha or _ means it's the bare $ operator
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(LexerA93, MultipleIdentTypes) {
  // §A.9.3: Mix of simple, escaped, and system identifiers in one source.
  auto tokens = Lex("foo \\bar $baz");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "\\bar");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].text, "$baz");
}

// ---------------------------------------------------------------------------
// Multiple identifiers separated by tokens
// ---------------------------------------------------------------------------

TEST(LexerA93, IdentifiersSeparatedByDot) {
  // §A.9.3: Dot-separated identifiers for hierarchical_identifier.
  auto tokens = Lex("a.b.c");
  ASSERT_GE(tokens.size(), 6u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].text, "b");
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].text, "c");
}

TEST(LexerA93, IdentifiersSeparatedByColonColon) {
  // §A.9.3: :: separates package_scope identifiers.
  auto tokens = Lex("pkg::item");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "pkg");
  EXPECT_EQ(tokens[1].kind, TokenKind::kColonColon);
  EXPECT_EQ(tokens[2].text, "item");
}
