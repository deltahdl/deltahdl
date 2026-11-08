#include <gtest/gtest.h>

#include "fixture_lexer.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConstraintDistLexing, DistKeywordRecognised) {
  auto r = LexOne("dist");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDist);
}

TEST(ConstraintDistLexing, DefaultKeywordRecognised) {
  auto r = LexOne("default");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDefault);
}

}  // namespace
