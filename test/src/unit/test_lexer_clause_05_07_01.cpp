#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// §5.7.1: whitespace is permitted between the size and the apostrophe and
// between the apostrophe and the base specifier — a main-text rule that
// the §A.8.7 BNF does not itself express.

TEST(IntegerLiteralLexing, WhitespaceSizeAndBase) {
  auto r = LexOne("5 'D 3 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

TEST(IntegerLiteralLexing, WhitespaceBaseAndDigits) {
  auto r = LexOne("32 'h 12ab_f001 ");
  EXPECT_EQ(r.token.kind, TokenKind::kIntLiteral);
}

// §5.7.1: whitespace separates adjacent numeric tokens — a lexical
// boundary rule that the §A.8.7 BNF does not itself express.
TEST(IntegerLiteralLexing, SpaceBreaksNumberIntoTwo) {
  auto tokens = Lex("12 34");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIntLiteral);
}

}  // namespace
