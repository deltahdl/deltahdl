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

TEST(IdentifierLexing, EscapedIdentifierWithSpecialChars) {
  auto tokens = Lex("\\busy-signal+ ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "busy-signal+");
}

TEST(IdentifierLexing, EscapedIdentifierTerminatedByNewline) {
  auto tokens = Lex("\\foo\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
}

TEST(IdentifierLexing, EscapedSystemTfIdentifierIsEscapedNotSystemIdent) {
  auto tokens = Lex("\\$display ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
}

TEST(IdentifierLexing, SystemIdentDigitAsFirstBodyChar) {
  auto tokens = Lex("$0 ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$0");
}

TEST(IdentifierLexing, SystemIdentUnderscoreAsFirstBodyChar) {
  auto tokens = Lex("$_my_task ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$_my_task");
}

TEST(IdentifierLexing, SystemIdentSingleCharBody) {
  auto tokens = Lex("$a ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$a");
}

TEST(IdentifierLexing, SystemIdentUppercaseBody) {
  auto tokens = Lex("$ABC ");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$ABC");
}

TEST(IdentifierLexing, SystemIdentTrailingDollar) {
  auto tokens = Lex("$test$ ;");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$");
}

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

TEST(IdentifierLexing, SimpleIdentLeadingUnderscore) {
  auto tokens = Lex("_foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "_foo");
}

TEST(IdentifierLexing, EscapedIdentifierTerminatedByEof) {
  auto tokens = Lex("\\foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "foo");
}

TEST(IdentifierLexing, SystemIdentDollarAsFirstBodyChar) {
  auto tokens = Lex("$$bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$$bar");
}

TEST(IdentifierLexing, SimpleIdentAllowsTrailingUnderscores) {
  auto tokens = Lex("foo___");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "foo___");
}

TEST(IdentifierLexing, SimpleIdentFirstCharCannotBeDigit) {
  auto tokens = Lex("9abc");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_NE(tokens[0].kind, TokenKind::kIdentifier);
}

TEST(IdentifierLexing, EscapedIdentifierTerminatedByTab) {
  auto tokens = Lex("\\x_y\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "x_y");
}

TEST(IdentifierLexing, EscapedIdentifierRejectsControlChar) {
  std::string src = "\\foo";
  src.push_back(static_cast<char>(0x07));
  src.append(" rest");
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, SimpleIdentMaxLength) {
  std::string id(1024, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(IdentifierLexing, SimpleIdentExceedsMaxLength) {
  std::string id(1025, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(IdentifierLexing, EscapedIdentifierMaxLength) {
  std::string src = "\\" + std::string(1024, 'q') + " ";
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(IdentifierLexing, EscapedIdentifierExceedsMaxLength) {
  std::string src = "\\" + std::string(1025, 'q') + " ";
  auto [tokens, errors] = LexWithDiag(src);
  EXPECT_TRUE(errors);
}
