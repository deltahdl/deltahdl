#include <gtest/gtest.h>

#include <set>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(LexicalConventionLexing, TokenStreamEndsWithEof) {
  auto tokens = Lex("module m; endmodule");
  ASSERT_FALSE(tokens.empty());
  EXPECT_EQ(tokens.back().kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, EmptySourceProducesOnlyEof) {
  auto tokens = Lex("");
  ASSERT_EQ(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kEof);
}

TEST(LexicalConventionLexing, LineCommentIsStripped) {
  auto tokens = Lex("a // comment\nb");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, BlockCommentIsStripped) {
  auto tokens = Lex("a /* block */ b");
  ASSERT_EQ(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].text, "a");
  EXPECT_EQ(tokens[1].text, "b");
}

TEST(LexicalConventionLexing, OperatorTokensRecognized) {
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

TEST(LexicalConventionLexing, KeywordDistinctFromIdentifier) {
  auto kw = LexOne("module");
  EXPECT_EQ(kw.token.kind, TokenKind::kKwModule);

  auto id = LexOne("my_module");
  EXPECT_EQ(id.token.kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, IntegerLiteralRecognized) {
  auto r = LexOne("32'd100");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, RealLiteralRecognized) {
  auto r = LexOne("3.14");
  EXPECT_EQ(r.token.kind, TokenKind::kRealLiteral);
}

TEST(LexicalConventionLexing, StringLiteralRecognized) {
  auto r = LexOne("\"hello world\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, TimeLiteralRecognized) {
  auto r = LexOne("10ns");
  EXPECT_EQ(r.token.kind, TokenKind::kTimeLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedLiteralRecognized) {
  auto r = LexOne("'1");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
}

TEST(LexicalConventionLexing, ArrayStructLiteralTokenRecognized) {
  auto r = LexOne("'{");
  EXPECT_EQ(r.token.kind, TokenKind::kApostropheLBrace);
}

TEST(LexicalConventionLexing, TripleQuotedStringLiteralRecognized) {
  auto r = LexOne("\"\"\"hello\"\"\"");
  EXPECT_EQ(r.token.kind, TokenKind::kStringLiteral);
}

TEST(LexicalConventionLexing, EscapedIdentifierRecognized) {
  auto r = LexOne("\\busa+index ");
  EXPECT_EQ(r.token.kind, TokenKind::kEscapedIdentifier);
}

TEST(LexicalConventionLexing, SystemIdentifierRecognized) {
  auto r = LexOne("$display");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
}

TEST(LexicalConventionLexing, SystemIdentifierPreservesDollarPrefix) {
  auto r = LexOne("$finish");
  EXPECT_EQ(r.token.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(r.token.text, "$finish");
}

TEST(LexicalConventionLexing, DotTokenForBuiltinMethodCalls) {
  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexicalConventionLexing, AttributeStartTokenRecognized) {
  auto r = LexOne("(*");
  EXPECT_EQ(r.token.kind, TokenKind::kAttrStart);
}

TEST(LexicalConventionLexing, AttributeEndTokenRecognized) {
  auto tokens = Lex("(* foo *)");
  ASSERT_GE(tokens.size(), 4u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(LexicalConventionLexing, AllFourAreasInOneStream) {
  auto tokens =
      Lex("(* full_case *) module t; // comment\n"
          "  logic [7:0] x = 8'hFF + 1;\n"
          "  real r = 3.14;\n"
          "  initial $display(\"msg\");\n"
          "endmodule\n");

  std::set<TokenKind> kinds;
  for (const auto& tok : tokens) {
    kinds.insert(tok.kind);
  }

  EXPECT_TRUE(kinds.count(TokenKind::kAttrStart));
  EXPECT_TRUE(kinds.count(TokenKind::kKwModule));
  EXPECT_TRUE(kinds.count(TokenKind::kPlus));
  EXPECT_TRUE(kinds.count(TokenKind::kIntLiteral));
  EXPECT_TRUE(kinds.count(TokenKind::kRealLiteral));
  EXPECT_TRUE(kinds.count(TokenKind::kStringLiteral));
  EXPECT_TRUE(kinds.count(TokenKind::kSystemIdentifier));
  EXPECT_TRUE(kinds.count(TokenKind::kIdentifier));
}

TEST(LexicalConventionLexing, UnterminatedBlockCommentIsError) {
  auto r = LexWithDiag("a /* unterminated");
  EXPECT_TRUE(r.has_errors);
}

TEST(LexicalConventionLexing, UnterminatedStringIsError) {
  auto r = LexWithDiag("\"unterminated");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
