#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_6_SimpleIdentLetters) {
  auto r = LexOne("abc ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "abc");
}

TEST(LexerClause05, Cl5_6_SimpleIdentDigits) {
  auto r = LexOne("val42 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "val42");
}

TEST(LexerClause05, Cl5_6_SimpleIdentUnderscore) {
  auto r = LexOne("_bus3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "_bus3");
}

TEST(LexerClause05, Cl5_6_SimpleIdentDollar) {
  auto r = LexOne("n$657 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "n$657");
}

TEST(LexerClause05, Cl5_6_SimpleIdentMixed) {
  auto r = LexOne("abc_123$xyz ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "abc_123$xyz");
}

TEST(LexerClause05, Cl5_6_LrmExampleShiftreg) {
  auto r = LexOne("shiftreg_a ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "shiftreg_a");
}

TEST(LexerClause05, Cl5_6_LrmExampleBusaIndex) {
  auto r = LexOne("busa_index ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "busa_index");
}

TEST(LexerClause05, Cl5_6_LrmExampleError_condition) {
  auto r = LexOne("error_condition ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "error_condition");
}

TEST(LexerClause05, Cl5_6_LrmExampleMerge_ab) {
  auto r = LexOne("merge_ab ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "merge_ab");
}

TEST(LexerClause05, Cl5_6_LrmExampleData0) {
  auto r = LexOne("_data_3_ ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "_data_3_");
}

TEST(LexerClause05, Cl5_6_DigitStartIsNumber) {
  auto r = LexOne("42abc ");

  EXPECT_NE(r.token.kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_6_DollarStartIsSystemOrDollar) {
  auto r = LexOne("$finish ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(LexerClause05, Cl5_6_BareDollarIsDollarToken) {
  auto r = LexOne("$ ");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

TEST(LexerClause05, Cl5_6_CaseSensitive) {
  auto tokens = Lex("ABC abc Abc");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].text, "ABC");
  EXPECT_EQ(tokens[1].text, "abc");
  EXPECT_EQ(tokens[2].text, "Abc");
}

TEST(LexerClause05, Cl5_6_KeywordRecognized) {
  auto r = LexOne("module ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(LexerClause05, Cl5_6_UppercaseNotKeyword) {
  auto r = LexOne("Module ");
  EXPECT_EQ(r.token.kind, TokenKind::kIdentifier);
  EXPECT_EQ(r.token.text, "Module");
}

TEST(LexerClause05, Cl5_6_MaxLength1024Ok) {
  std::string id(1024, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text.size(), 1024u);
}

TEST(LexerClause05, Cl5_6_MaxLength1025Error) {
  std::string id(1025, 'a');
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_6_EscapedMaxLength1025Error) {
  std::string id = "\\" + std::string(1025, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_TRUE(errors);
}

TEST(LexerClause05, Cl5_6_SimpleAndEscapedInStream) {
  auto tokens = Lex("abc \\def ghi");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[0].text, "abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "\\def");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].text, "ghi");
}

}  // namespace
