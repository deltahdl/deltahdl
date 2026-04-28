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

