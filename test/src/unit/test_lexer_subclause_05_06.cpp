#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"

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
  auto tokens = Lex("42abc ");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[0].text, "42");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "abc");
}

TEST(LexicalConventionLexing, DollarStartIsNotIdentifier) {
  auto r = LexOne("$abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$abc");
}

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
