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

TEST(LexicalConventionLexing, IntegerLiteralRecognized) {
  auto r = LexOne("32'd100");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(LexicalConventionLexing, UnbasedUnsizedLiteralRecognized) {
  auto r = LexOne("'1");
  EXPECT_EQ(r.token.kind, TokenKind::kUnbasedUnsizedLiteral);
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

}  // namespace
