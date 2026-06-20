#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(AlwaysFFLexing, AlwaysFFKeyword) {
  auto r = LexOne("always_ff ");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAlwaysFF);
  EXPECT_EQ(r.token.text, "always_ff");
}

}  // namespace
