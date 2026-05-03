#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

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

TEST(LexicalConventionLexing, DigitStartIsNumber) {
  auto r = LexOne("42abc ");

  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

// §5.6: "The first character of a simple identifier shall not be a digit
// or $". A leading $ followed by identifier characters is not a simple
// identifier (it is parsed elsewhere as a system name).
TEST(LexicalConventionLexing, DollarStartIsNotIdentifier) {
  auto r = LexOne("$abc ");
  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

// §5.6: "A keyword (see 5.6.2) may not be used as a user-defined
// identifier." A bare keyword form must not be classified as an identifier
// token by the lexer.
TEST(LexicalConventionLexing, KeywordIsNotIdentifier) {
  auto r = LexOne("module ");
  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
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
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexicalConventionLexing, EscapedMaxLength1025Error) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

// §5.6: "An identifier is either a simple identifier or an escaped
// identifier" and "the limit shall be at least 1024 characters". An
// escaped identifier whose body is exactly 1024 characters must lex as
// kEscapedIdentifier with no length error, observing both the categorical
// distinction and the boundary of the length floor on the escaped path.
TEST(LexicalConventionLexing, EscapedMaxLength1024Ok) {
  std::string id = "\\" + std::string(1024, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
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
