#include <gtest/gtest.h>

#include <string>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_6_1_BasicEscapedIdentifier) {
  auto r = LexOne("\\cpu3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "\\cpu3");
}

TEST(LexerClause05, Cl5_6_1_TerminatedBySpace) {
  auto tokens = Lex("\\esc_id next");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].text, "next");
}

TEST(LexerClause05, Cl5_6_1_TerminatedByNewline) {
  auto tokens = Lex("\\esc_id\n");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerClause05, Cl5_6_1_TerminatedByTab) {
  auto tokens = Lex("\\esc_id\t");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerClause05, Cl5_6_1_TerminatedByEof) {
  auto tokens = Lex("\\esc_id");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\esc_id");
}

TEST(LexerClause05, Cl5_6_1_SpecialCharsInEscaped) {
  auto r = LexOne("\\***error-condition*** ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "\\***error-condition***");
}

TEST(LexerClause05, Cl5_6_1_ForwardSlash) {
  auto r = LexOne("\\net1/\\net2 ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "\\net1/\\net2");
}

TEST(LexerClause05, Cl5_6_1_Braces) {
  auto r = LexOne("\\{a,b} ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "\\{a,b}");
}

TEST(LexerClause05, Cl5_6_1_PlusSign) {
  auto r = LexOne("\\busa+index ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(r.token.text, "\\busa+index");
}

TEST(LexerClause05, Cl5_6_1_EscapedKeywordIsIdentifier) {
  auto r = LexOne("\\module ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
  EXPECT_NE(r.token.kind, TokenKind::kKwModule);
}

TEST(LexerClause05, Cl5_6_1_EscapedBeginIsIdentifier) {
  auto r = LexOne("\\begin ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
}

TEST(LexerClause05, Cl5_6_1_MaxLengthOk) {
  std::string id = "\\" + std::string(1023, 'a') + " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
}

TEST(LexerClause05, Cl5_6_1_MultipleEscapedInSequence) {
  auto tokens = Lex("\\abc \\def \\ghi ");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[0].text, "\\abc");
  EXPECT_EQ(tokens[1].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[1].text, "\\def");
  EXPECT_EQ(tokens[2].kind, TokenKind::kEscapedIdentifier);
  EXPECT_EQ(tokens[2].text, "\\ghi");
}

}
