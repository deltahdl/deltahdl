#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

TEST(IdentifierLexing, SimpleIdentSingleChar) {
  auto tokens = Lex("a");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "a");
}

TEST(IdentifierLexing, SimpleIdentSingleUnderscore) {
  auto tokens = Lex("_");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_");
}

TEST(IdentifierLexing, SimpleIdentAllAlpha) {
  auto tokens = Lex("myIdentifier");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "myIdentifier");
}

TEST(IdentifierLexing, SimpleIdentAlphaNumUnderscore) {
  auto tokens = Lex("data_bus_32bit");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "data_bus_32bit");
}

TEST(IdentifierLexing, SimpleIdentWithDollar) {
  auto tokens = Lex("my$var");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "my$var");
}

TEST(IdentifierLexing, SimpleIdentStartUppercase) {
  auto tokens = Lex("Module_A");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "Module_A");
}

TEST(IdentifierLexing, SimpleIdentLeadingUnderscores) {
  auto tokens = Lex("__private_var");
  ASSERT_EQ(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "__private_var");
}

TEST(IdentifierLexing, SimpleIdentMaxLength) {
  std::string id(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(IdentifierLexing, SimpleIdentExceedsMaxLength) {
  std::string id(1025, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, SimpleIdentCaseSensitive) {
  auto tokens = Lex("foo FOO Foo");
  ASSERT_EQ(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "foo");
  EXPECT_EQ(tokens[1].text, "FOO");
  EXPECT_EQ(tokens[2].text, "Foo");
}

TEST(IdentifierLexing, SimpleIdentKeywordDisambiguation) {
  auto tokens = Lex("module");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwModule);
}

TEST(IdentifierLexing, SimpleIdentNotKeyword) {
  auto tokens = Lex("modules");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "modules");
}

TEST(IdentifierLexing, SimpleIdentSourceLocation) {
  auto [tokens, errors] = LexWithDiag("  foo");
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].loc.line, 1u);
  EXPECT_EQ(tokens[0].loc.column, 3u);
}

TEST(IdentifierLexing, EscapedIdentBasic) {
  auto tokens = Lex("\\my_id ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "my_id");
}

TEST(IdentifierLexing, EscapedIdentWithKeyword) {
  auto tokens = Lex("\\module ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "module");
}

TEST(IdentifierLexing, EscapedIdentWithSpecialChars) {
  auto tokens = Lex("\\a+b*c/d ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "a+b*c/d");
}

TEST(IdentifierLexing, EscapedIdentTerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(IdentifierLexing, EscapedIdentTerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "esc_id");
}

TEST(IdentifierLexing, EscapedIdentWithBraces) {
  auto tokens = Lex("\\{net} ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "{net}");
}

TEST(IdentifierLexing, EscapedIdentWithBrackets) {
  auto tokens = Lex("\\bus[0] ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "bus[0]");
}

TEST(IdentifierLexing, EscapedIdentMaxLength) {
  std::string id = "\\" + std::string(1023, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

TEST(IdentifierLexing, EscapedIdentExceedsMaxLength) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, EscapedIdentFollowedByToken) {
  auto tokens = Lex("\\my_id ; \\next_id ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "my_id");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSemicolon);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[2].text, "next_id");
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

TEST(IdentifierLexing, SystemIdBasic) {
  auto tokens = Lex("$display");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(IdentifierLexing, SystemIdWithUnderscore) {
  auto tokens = Lex("$read_mem_h");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$read_mem_h");
}

TEST(IdentifierLexing, SystemIdWithDigits) {
  auto tokens = Lex("$clog2");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$clog2");
}

TEST(IdentifierLexing, SystemIdEmbeddedDollar) {
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(IdentifierLexing, SystemIdMaxLength) {
  std::string id = "$" + std::string(1023, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(IdentifierLexing, SystemIdExceedsMaxLength) {
  std::string id = "$" + std::string(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, DollarAloneIsNotSystemId) {
  auto tokens = Lex("$ ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(IdentifierLexing, DollarFollowedByDigit) {
  auto tokens = Lex("$0");
  ASSERT_GE(tokens.size(), 2u);

  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
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
