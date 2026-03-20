#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(BlockKeywordLexing, BeginKeyword) {
  auto r = LexOne("begin");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBegin);
}

TEST(BlockKeywordLexing, EndKeyword) {
  auto r = LexOne("end");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEnd);
}

TEST(BlockKeywordLexing, ForkKeyword) {
  auto r = LexOne("fork");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFork);
}

TEST(BlockKeywordLexing, JoinKeyword) {
  auto r = LexOne("join");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoin);
}

TEST(BlockKeywordLexing, JoinAnyKeyword) {
  auto r = LexOne("join_any");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoinAny);
}

TEST(BlockKeywordLexing, JoinNoneKeyword) {
  auto r = LexOne("join_none");
  EXPECT_EQ(r.token.kind, TokenKind::kKwJoinNone);
}

}  // namespace
