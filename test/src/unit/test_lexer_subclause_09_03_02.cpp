#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(ParallelBlockLexing, ForkKeyword) {
  auto r = LexOne("fork ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFork);
  EXPECT_EQ(r.token.text, "fork");
}

TEST(ParallelBlockLexing, JoinKeyword) {
  auto r = LexOne("join ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoin);
  EXPECT_EQ(r.token.text, "join");
}

TEST(ParallelBlockLexing, JoinAnyKeyword) {
  auto r = LexOne("join_any ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(r.token.text, "join_any");
}

TEST(ParallelBlockLexing, JoinNoneKeyword) {
  auto r = LexOne("join_none ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(r.token.text, "join_none");
}

}  // namespace
