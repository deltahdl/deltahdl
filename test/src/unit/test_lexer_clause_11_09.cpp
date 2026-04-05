#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

TEST(TaggedUnionExprLexing, TaggedKeywordToken) {
  auto tokens = Lex("tagged");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTagged);
}

TEST(TaggedUnionExprLexing, TaggedMemberSequence) {
  auto tokens = Lex("tagged Valid 42");
  ASSERT_GE(tokens.size(), 4);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwTagged);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIntegerLiteral);
}
