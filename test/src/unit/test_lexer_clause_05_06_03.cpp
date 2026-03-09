#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_6_3_BasicSystemIdentifier) {
  auto r = LexOne("$display ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$display");
}

TEST(LexerClause05, Cl5_6_3_SystemFinish) {
  auto r = LexOne("$finish ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$finish");
}

TEST(LexerClause05, Cl5_6_3_SystemTime) {
  auto r = LexOne("$time ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$time");
}

TEST(LexerClause05, Cl5_6_3_EmbeddedDollar) {
  auto tokens = Lex("$test$plusargs $value$plusargs");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$test$plusargs");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$value$plusargs");
}

TEST(LexerClause05, Cl5_6_3_BareDollarNotSystemId) {
  auto r = LexOne("$ ");
  EXPECT_EQ(r.token.kind, TokenKind::kDollar);
}

TEST(LexerClause05, Cl5_6_3_DigitsInName) {
  auto r = LexOne("$sformat ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$sformat");
}

TEST(LexerClause05, Cl5_6_3_UnderscoreInName) {
  auto r = LexOne("$read_mem ");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$read_mem");
}

TEST(LexerClause05, Cl5_6_3_MaxLengthOk) {
  std::string id = "$" + std::string(1023, 'a');
  id += " ";
  auto [tokens, errors] = LexWithDiag(id);
  EXPECT_FALSE(errors);
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
}

TEST(LexerClause05, Cl5_6_3_MultipleInStream) {
  auto tokens = Lex("$display $finish $time");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[0].text, "$display");
  EXPECT_EQ(tokens[1].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[1].text, "$finish");
  EXPECT_EQ(tokens[2].kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(tokens[2].text, "$time");
}

}  // namespace
