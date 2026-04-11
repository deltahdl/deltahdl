#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(AlwaysProcedureLexing, AlwaysCombKeyword) {
  auto r = LexOne("always_comb ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysComb);
  EXPECT_EQ(r.token.text, "always_comb");
}

}  // namespace
