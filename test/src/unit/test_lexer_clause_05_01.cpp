#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexerClause05, Cl5_1_TokenStreamEndsWithEof) {
  auto tokens = Lex("module m; endmodule");
  ASSERT_FALSE(tokens.empty());
  EXPECT_EQ(tokens.back().kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_1_EmptySourceProducesOnlyEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_1_WhitespaceOnlyProducesEof) {
  auto tokens = Lex("   \t\n\n  ");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_1_WhitespaceIsNotEmittedAsToken) {
  auto tokens = Lex("a  b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEof);
}

TEST(LexerClause05, Cl5_1_LineCommentIsStripped) {
  auto tokens = Lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_1_BlockCommentIsStripped) {
  auto tokens = Lex("a /* block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexerClause05, Cl5_1_OperatorTokensRecognized) {
  auto tokens = Lex("+ - * / % ** && ||");
  EXPECT_EQ(tokens[0].kind, TokenKind::kPlus);
  EXPECT_EQ(tokens[1].kind, TokenKind::kMinus);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
  EXPECT_EQ(tokens[3].kind, TokenKind::kSlash);
  EXPECT_EQ(tokens[4].kind, TokenKind::kPercent);
  EXPECT_EQ(tokens[5].kind, TokenKind::kPower);
  EXPECT_EQ(tokens[6].kind, TokenKind::kAmpAmp);
  EXPECT_EQ(tokens[7].kind, TokenKind::kPipePipe);
}

TEST(LexerClause05, Cl5_1_KeywordDistinctFromIdentifier) {
  auto kw = LexOne("module");
  EXPECT_EQ(kw.token.kind, TokenKind::kKwModule);

  auto id = LexOne("my_module");
  EXPECT_EQ(id.token.kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_1_IntegerLiteralRecognized) {
  auto r = LexOne("32'd100");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexerClause05, Cl5_1_RealLiteralRecognized) {
  auto r = LexOne("3.14");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(LexerClause05, Cl5_1_StringLiteralRecognized) {
  auto r = LexOne("\"hello world\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_1_TimeLiteralRecognized) {
  auto r = LexOne("10ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
}

TEST(LexerClause05, Cl5_1_UnbasedUnsizedLiteralRecognized) {
  auto r = LexOne("'1");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexerClause05, Cl5_1_ArrayStructLiteralTokenRecognized) {
  auto r = LexOne("'{");
  EXPECT_EQ(r.token.kind, TokenKind::kApostropheLBrace);
}

TEST(LexerClause05, Cl5_1_TripleQuotedStringLiteralRecognized) {
  auto r = LexOne("\"\"\"hello\"\"\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexerClause05, Cl5_1_EscapedIdentifierRecognized) {
  auto r = LexOne("\\busa+index ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
}

TEST(LexerClause05, Cl5_1_SystemIdentifierRecognized) {
  auto r = LexOne("$display");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(LexerClause05, Cl5_1_SystemIdentifierPreservesDollarPrefix) {
  auto r = LexOne("$finish");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$finish");
}

TEST(LexerClause05, Cl5_1_DotTokenForBuiltinMethodCalls) {
  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_1_AttributeStartTokenRecognized) {
  auto r = LexOne("(*");
  EXPECT_EQ(r.token.kind, TokenKind::kAttrStart);
}

TEST(LexerClause05, Cl5_1_AttributeEndTokenRecognized) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(LexerClause05, Cl5_1_AllFourAreasInOneStream) {
  auto tokens =
      Lex("(* full_case *) module t; // comment\n"
          "  logic [7:0] x = 8'hFF + 1;\n"
          "  real r = 3.14;\n"
          "  initial $display(\"msg\");\n"
          "endmodule\n");

  bool has_attr_start = false;
  bool has_keyword = false;
  bool has_operator = false;
  bool has_int_literal = false;
  bool has_real_literal = false;
  bool has_string_literal = false;
  bool has_system_id = false;
  bool has_identifier = false;

  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kAttrStart) has_attr_start = true;
    if (tok.kind == TokenKind::kKwModule) has_keyword = true;
    if (tok.kind == TokenKind::kPlus) has_operator = true;
    if (tok.kind == TokenKind::kIntLiteral) has_int_literal = true;
    if (tok.kind == TokenKind::kRealLiteral) has_real_literal = true;
    if (tok.kind == TokenKind::kStringLiteral) has_string_literal = true;
    if (tok.kind == TokenKind::kSystemIdentifier) has_system_id = true;
    if (tok.kind == TokenKind::kIdentifier) has_identifier = true;
  }

  EXPECT_TRUE(has_attr_start);
  EXPECT_TRUE(has_keyword);
  EXPECT_TRUE(has_operator);
  EXPECT_TRUE(has_int_literal);
  EXPECT_TRUE(has_real_literal);
  EXPECT_TRUE(has_string_literal);
  EXPECT_TRUE(has_system_id);
  EXPECT_TRUE(has_identifier);
}

TEST(LexerClause05, Cl5_1_UnterminatedBlockCommentIsError) {
  auto r = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(r.has_errors);
}

TEST(LexerClause05, Cl5_1_UnterminatedStringIsError) {
  auto r = LexWithDiag("\"unterminated");
  EXPECT_TRUE(r.has_errors);
}

}
