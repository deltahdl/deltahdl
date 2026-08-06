#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ForceReleaseLexing, ForceKeyword) {
  auto r = LexOne("force");
  EXPECT_EQ(r.token.kind, TokenKind::kKwForce);
}

TEST(ForceReleaseLexing, ReleaseKeyword) {
  auto r = LexOne("release");
  EXPECT_EQ(r.token.kind, TokenKind::kKwRelease);
}

TEST(ForceReleaseLexing, ForceStatementTokenSequence) {
  auto tokens = Lex("force q = 1 ;");
  ASSERT_GE(tokens.size(), 5u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwForce);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kEq);
  EXPECT_EQ(tokens[3].kind, TokenKind::kIntLiteral);
  EXPECT_EQ(tokens[4].kind, TokenKind::kSemicolon);
}

TEST(ForceReleaseLexing, ReleaseStatementTokenSequence) {
  auto tokens = Lex("release q ;");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwRelease);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[2].kind, TokenKind::kSemicolon);
}

}  // namespace
