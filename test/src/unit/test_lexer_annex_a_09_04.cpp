// §A.9.4 White space — lexer-level tests

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
// §A.9.4 / §5.3: white_space ::= space | tab | newline | formfeed | eof
// BNF clarification 56: eof means "End of file."
// ===========================================================================

// ---------------------------------------------------------------------------
// Individual white_space characters as token separators
// ---------------------------------------------------------------------------

TEST(LexerA94, SpaceSeparatesTokens) {
  // §A.9.4: space is white_space; §5.3: separates lexical tokens.
  auto tokens = Lex("a b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "b");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexerA94, TabSeparatesTokens) {
  // §A.9.4: tab is white_space; §5.3: separates lexical tokens.
  auto tokens = Lex("a\tb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, NewlineSeparatesTokens) {
  // §A.9.4: newline is white_space; §5.3: separates lexical tokens.
  auto tokens = Lex("a\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, FormfeedSeparatesTokens) {
  // §A.9.4: formfeed is white_space; §5.3: separates lexical tokens.
  auto tokens = Lex("a\fb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, EofTerminatesTokenStream) {
  // §A.9.4 / Clarification 56: eof is white_space (end of file).
  // The final token in every token stream shall be kEof.
  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerA94, EofOnEmptyInput) {
  // §A.9.4 / Clarification 56: Empty source produces only an eof token.
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// ---------------------------------------------------------------------------
// §5.3: White space characters shall be ignored except when they serve
// to separate other lexical tokens.
// ---------------------------------------------------------------------------

TEST(LexerA94, WhitespaceIgnoredBetweenOperators) {
  // §5.3: Operators do not require whitespace separation.
  auto tokens = Lex("a+b");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[2].text, "b");
}

TEST(LexerA94, MultipleSpacesIgnored) {
  // §5.3: Multiple spaces are equivalent to one.
  auto tokens = Lex("a     b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, MixedWhitespaceIgnored) {
  // §5.3: Mixed white_space characters all ignored equally.
  auto tokens = Lex("a \t \n \f b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, LeadingWhitespaceIgnored) {
  // §5.3: White space before first token is ignored.
  auto tokens = Lex("  \t\n  a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(LexerA94, TrailingWhitespaceIgnored) {
  // §5.3: White space after last token is ignored.
  auto tokens = Lex("a  \t\n  ");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEof);
}

TEST(LexerA94, OnlyWhitespaceInput) {
  // §5.3: Source containing only white space yields only eof.
  auto tokens = Lex("   \t\t\n\n\f  ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

// ---------------------------------------------------------------------------
// §5.3: White space required to separate keywords/identifiers
// ---------------------------------------------------------------------------

TEST(LexerA94, WhitespaceRequiredBetweenKeywords) {
  // §5.3: Without whitespace, "moduleendmodule" is one identifier, not two keywords.
  auto tokens = Lex("moduleendmodule");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "moduleendmodule");
}

TEST(LexerA94, WhitespaceCorrectlySeparatesKeywords) {
  // §5.3: Space separates "module" and "endmodule" into distinct keywords.
  auto tokens = Lex("module endmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, FormfeedSeparatesKeywords) {
  // §A.9.4: Formfeed is white_space and separates keywords.
  auto tokens = Lex("module\fendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, TabSeparatesKeywords) {
  auto tokens = Lex("module\tendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

TEST(LexerA94, NewlineSeparatesKeywords) {
  auto tokens = Lex("module\nendmodule");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
  EXPECT_EQ(tokens[1].kind, TokenKind::kKwEndmodule);
}

// ---------------------------------------------------------------------------
// Source location tracking across white_space characters
// ---------------------------------------------------------------------------

TEST(LexerA94, NewlineAdvancesLineNumber) {
  // §A.9.4: newline advances the line counter.
  auto [tokens, errors] = LexWithDiag("a\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 2u);
}

TEST(LexerA94, TabAdvancesColumn) {
  // §A.9.4: tab advances the column counter.
  auto [tokens, errors] = LexWithDiag("a\tb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(LexerA94, FormfeedAdvancesColumn) {
  // §A.9.4: formfeed advances the column counter (not line).
  auto [tokens, errors] = LexWithDiag("a\fb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.column, 3u);
}

TEST(LexerA94, MultipleNewlinesTrackCorrectly) {
  auto [tokens, errors] = LexWithDiag("a\n\n\nb");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[1].loc.line, 4u);
}

TEST(LexerA94, SpaceAdvancesColumn) {
  auto [tokens, errors] = LexWithDiag("a   b");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].loc.column, 1u);
  EXPECT_EQ(tokens[1].loc.column, 5u);
}

// ---------------------------------------------------------------------------
// Carriage return and vertical tab (C++ std::isspace extensions)
// ---------------------------------------------------------------------------

TEST(LexerA94, CarriageReturnIsWhitespace) {
  // \r is treated as whitespace by std::isspace; separates tokens.
  auto tokens = Lex("a\rb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, VerticalTabIsWhitespace) {
  // \v is treated as whitespace by std::isspace; separates tokens.
  auto tokens = Lex("a\vb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerA94, CrLfPairIsWhitespace) {
  // \r\n (Windows line ending) is handled as whitespace.
  auto tokens = Lex("a\r\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

// ---------------------------------------------------------------------------
// §A.9.3 cross-reference: escaped_identifier terminated by white_space
// ---------------------------------------------------------------------------

TEST(LexerA94, EscapedIdentTerminatedBySpace) {
  // §A.9.3/§A.9.4: space is white_space; terminates escaped_identifier.
  auto tokens = Lex("\\esc_id ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByFormfeed) {
  // §A.9.4: formfeed is white_space; terminates escaped_identifier.
  auto tokens = Lex("\\esc_id\f");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerA94, EscapedIdentTerminatedByEof) {
  // §A.9.4 / Clarification 56: eof is white_space; terminates escaped_identifier.
  auto tokens = Lex("\\esc_id");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

// ---------------------------------------------------------------------------
// §5.3: Blanks and tabs shall be considered significant in string literals
// ---------------------------------------------------------------------------

TEST(LexerA94, StringLiteralPreservesSpaces) {
  // §5.3: Blanks are significant in string literals.
  auto tokens = Lex("\"a b c\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a b c\"");
}

TEST(LexerA94, StringLiteralPreservesTabs) {
  // §5.3: Tabs are significant in string literals.
  auto tokens = Lex("\"a\tb\"");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kStringLiteral);
  EXPECT_EQ(tokens[0].text, "\"a\tb\"");
}

// ---------------------------------------------------------------------------
// No diagnostics for valid white_space usage
// ---------------------------------------------------------------------------

TEST(LexerA94, NoErrorsForAllWhitespaceTypes) {
  // All five A.9.4 white_space characters used in valid source.
  auto [tokens, errors] = LexWithDiag(
      "module m;\n"
      "\tlogic\fa;\n"
      "endmodule\n");
  EXPECT_FALSE(errors);
}

TEST(LexerA94, NoErrorsForWhitespaceOnlySource) {
  auto [tokens, errors] = LexWithDiag("   \t\n\f  ");
  EXPECT_FALSE(errors);
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}
