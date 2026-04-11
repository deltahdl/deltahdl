#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(AlwaysProcedureLexing, AlwaysCombKeyword) {
  auto r = LexOne("always_comb ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysComb);
  EXPECT_EQ(r.token.text, "always_comb");
}

TEST(AlwaysProcedureLexing, AlwaysLatchKeyword) {
  auto r = LexOne("always_latch ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysLatch);
  EXPECT_EQ(r.token.text, "always_latch");
}

TEST(AlwaysProcedureLexing, AlwaysFFKeyword) {
  auto r = LexOne("always_ff ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysFF);
  EXPECT_EQ(r.token.text, "always_ff");
}

}  // namespace
