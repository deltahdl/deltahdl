#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ContAssignDelayLexing, SingleDelayTokenStream) {
  auto tokens = Lex("assign #5 out = in;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].text, "5");
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[4].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[6].kind, TokenKind::kSemicolon);
}

TEST(ContAssignDelayLexing, ParenthesizedTwoDelayTokenStream) {
  auto tokens = Lex("assign #(5, 10) out = in;");
  ASSERT_GE(tokens.size(), 11u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[3].text, "5");
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[5].text, "10");
  EXPECT_EQ(tokens[6].kind, TokenKind::kRParen);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[8].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[9].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[10].kind, TokenKind::kSemicolon);
}

TEST(ContAssignDelayLexing, ParenthesizedThreeDelayTokenStream) {
  auto tokens = Lex("assign #(5, 10, 15) out = in;");
  ASSERT_GE(tokens.size(), 13u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwAssign);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[5].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[6].kind, TokenKind::kComma);
  EXPECT_EQ(tokens[7].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[8].kind, TokenKind::kRParen);
}

TEST(ContAssignDelayLexing, NetDeclDelayWithInitTokenStream) {
  auto tokens = Lex("wire #3 w = 1'b0;");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwWire);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[2].text, "3");
  EXPECT_EQ(tokens[3].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].text, "w");
  EXPECT_EQ(tokens[4].kind, TokenKind::kEq);
}

}  // namespace
