#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(SequentialBlockLexing, BeginKeyword) {
  auto r = LexOne("begin ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwBegin);
  EXPECT_EQ(r.token.text, "begin");
}

TEST(SequentialBlockLexing, EndKeyword) {
  auto r = LexOne("end ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEnd);
  EXPECT_EQ(r.token.text, "end");
}

}  // namespace
