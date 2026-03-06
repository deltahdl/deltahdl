#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- §5.13: built-in method call token sequences ---

TEST(LexerClause05, Cl5_13_DotNotationTokens) {
  // object.method() — dot notation for built-in methods
  auto tokens = Lex("arr.size()");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[4].kind, TokenKind::kRParen);
}

TEST(LexerClause05, Cl5_13_DotNotationNoParens) {
  // object.method — optional empty parens
  auto tokens = Lex("arr.size");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_13_ChainedDotNotation) {
  // obj.arr.size() — chained member access
  auto tokens = Lex("obj.arr.size()");
  ASSERT_GE(tokens.size(), 7u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[4].kind, TokenKind::kIdentifier);
}

TEST(LexerClause05, Cl5_13_MethodWithArgTokens) {
  // q.push_back(8'hAA) — method with argument
  auto tokens = Lex("q.push_back(8'hAA)");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kDot);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[3].kind, TokenKind::kLParen);
}

}  // namespace
